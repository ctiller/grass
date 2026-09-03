//! The host coordinator (docs/AGENT_COORDINATION_EVOLUTION.md section 2.3).
//!
//! Not a persistent daemon: any CLI invocation may momentarily assume this
//! role by draining one agent's local outbox, validating and sequencing
//! each candidate, and constructing the resulting stream commit(s). "The
//! role owns policy, while a deterministic local helper may execute queue,
//! validation, fetch, and push mechanics so ordinary progress does not
//! depend on an LLM turn remaining alive" -- the mechanics here are exactly
//! that: deterministic, and requiring no ongoing process.
//!
//! Deliberately scoped for now: drains and publishes one agent's own
//! outbox in submission order, then pushes that agent's stream ref alone
//! (`publish_stream`/`drain_and_publish`, via `publish.rs`). No cross-agent
//! dependency-closure batching or multi-ref atomic publication yet -- those
//! matter once a single coordinator turn can affect more than one agent's
//! ref at a time (e.g. a registry transition alongside the stream event it
//! authorizes), and are real further work, not silently assumed away.

use crate::envelope::Envelope;
use crate::error::{invalid, AbError, AbResult};
use crate::frontier::{FrontierEntry, ObservedFrontier};
use crate::scalars::{Agent, EventId, Short};
use std::path::Path;

/// One candidate `drain_outbox` refused to publish, and why. The candidate
/// itself is never silently discarded -- see `drain_outbox`'s doc comment.
#[derive(Debug, Clone)]
pub struct RejectedCandidate {
    pub kind: String,
    pub reason: String,
}

/// What one `drain_outbox` call actually did: which candidates became real
/// stream events, and which were refused (with a durable local rejection
/// receipt still on disk -- see `reject_candidate`).
#[derive(Debug, Clone, Default)]
pub struct DrainResult {
    pub published: Vec<EventId>,
    pub rejected: Vec<RejectedCandidate>,
}

/// Drains every pending candidate in `agent`'s local outbox, in submission
/// order, and publishes the ones that pass validation as one or two new
/// stream commits (a root commit if this is the agent's first-ever event,
/// then a follow-on commit for the rest). An empty outbox is a no-op
/// returning `Ok(DrainResult::default())`.
///
/// Every candidate is validated with `apply::dry_run` against a local
/// reduction of everything currently known (`sync::cached_snapshot`) before
/// it is ever committed -- streams are append-only and force-pushes are
/// prohibited, so an accepted-but-malformed event could never be retracted,
/// and `apply::reduce`'s single `?` on the first error means one such event
/// would break *every* future cached or synced read, on every host that
/// ever pulls it, forever. A rejected candidate is instead removed from the
/// active outbox and written to a `rejected/` receipt alongside it --
/// durable local evidence, per section 2.3 ("A rejected candidate remains
/// local evidence; its author submits a replacement"), not silently
/// dropped and not left stuck in the outbox blocking every later candidate
/// from that agent's contiguous sequence.
///
/// This validates only against what is already *locally* known, not a
/// fresh remote probe -- a real, disclosed limitation: a candidate that is
/// actually valid but looks invalid only because this host's local view is
/// stale will be rejected and must be resubmitted, rather than the
/// coordinator silently fetching first. `sync::synced_snapshot` composed in
/// front of this call is how a caller avoids that.
///
/// `host`/`coordinator_custody_epoch` identify the caller's own claimed
/// custody, checked against the current registry epoch before anything is
/// written (gate 6/7's precondition, via `registry::authorize_stream_write`).
pub fn drain_outbox(
    repo: &Path,
    git_common_dir: &Path,
    agent: &Agent,
    host: &Short,
    coordinator_custody_epoch: u64,
    worktrees_dir: &Path,
) -> AbResult<DrainResult> {
    let pending = crate::outbox::list_pending(git_common_dir, agent)?;
    if pending.is_empty() {
        return Ok(DrainResult::default());
    }

    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists yet"))?;
    let epoch = crate::registry::read_epoch(repo, &registry_tip, &worktrees_dir.join("_epoch"))?;
    crate::registry::authorize_stream_write(&epoch, agent, host, coordinator_custody_epoch)?;

    let mut state = crate::sync::cached_snapshot(repo, &worktrees_dir.join("_validate"))?.state;

    let existing_tip = crate::stream::read_stream_tip(repo, agent)?;
    let mut next_seq = if existing_tip.is_some() {
        let reads_dir = worktrees_dir.join(format!("_read_{agent}"));
        crate::storage::read_stream_log(
            &{
                crate::gitrepo::ensure_bus_worktree(
                    repo,
                    &reads_dir,
                    existing_tip.as_ref().unwrap().as_str(),
                )?;
                reads_dir
            },
            agent,
        )?
        .len() as u64
    } else {
        0
    };

    let mut envelopes = Vec::with_capacity(pending.len());
    let mut rejected = Vec::new();
    for (path, candidate) in &pending {
        let data = candidate.typed_data()?;
        let observed = build_frontier(
            repo,
            &epoch,
            &worktrees_dir.join("_frontier"),
            agent,
            &candidate.extra_refs,
            &data,
        )?;
        let env = Envelope::new(
            agent,
            next_seq,
            observed,
            &data,
            candidate.extra_refs.clone(),
        );
        match crate::apply::dry_run(&state, &env) {
            Ok(()) => {
                state = crate::apply::reduce_onto(state, std::slice::from_ref(&env))?;
                envelopes.push((path.clone(), env));
                next_seq += 1;
            }
            Err(e) => {
                reject_candidate(git_common_dir, agent, path, candidate, &e.to_string())?;
                rejected.push(RejectedCandidate {
                    kind: candidate.kind.clone(),
                    reason: e.to_string(),
                });
            }
        }
    }

    let mut published = Vec::with_capacity(envelopes.len());
    let mut remaining: Vec<Envelope> = envelopes.iter().map(|(_, e)| e.clone()).collect();
    let mut new_tip = existing_tip;

    if new_tip.is_none() && !remaining.is_empty() {
        let first = remaining.remove(0);
        let header = crate::stream::StreamHeader {
            agent: agent.clone(),
            activation_event: None,
            registration_authority: first.id.clone(),
            final_v1_seq: None,
            object_format: state.config.object_format.clone(),
            schema_fingerprint: crate::bootstrap::SCHEMA_FINGERPRINT.to_string(),
        };
        let commit = crate::stream::create_root_commit(
            repo,
            &header,
            &first,
            &worktrees_dir.join(format!("_stream_root_{agent}")),
        )?;
        published.push(first.id);
        new_tip = Some(commit);
    }

    if !remaining.is_empty() {
        let commit = crate::stream::append_to_stream(
            repo,
            agent,
            new_tip.as_ref().expect("set above"),
            &remaining,
            &worktrees_dir.join(format!("_stream_append_{agent}")),
        )?;
        published.extend(remaining.iter().map(|e| e.id.clone()));
        let _ = commit;
    }

    for (path, _) in &envelopes {
        crate::outbox::remove(path)?;
    }

    Ok(DrainResult {
        published,
        rejected,
    })
}

/// Removes a rejected candidate from the active outbox and writes it,
/// alongside the reason, to a `rejected/` receipt in the same outbox
/// directory -- durable local evidence the author (or a human) can inspect,
/// without it blocking any later candidate's contiguous sequence.
fn reject_candidate(
    git_common_dir: &Path,
    agent: &Agent,
    path: &Path,
    candidate: &crate::outbox::Candidate,
    reason: &str,
) -> AbResult<()> {
    let rejected_dir = crate::outbox::outbox_dir(git_common_dir, agent).join("rejected");
    std::fs::create_dir_all(&rejected_dir).map_err(|e| AbError::Io {
        path: rejected_dir.display().to_string(),
        source: e,
    })?;
    let file_name = path.file_name().ok_or_else(|| {
        invalid(format!(
            "candidate path {} has no file name",
            path.display()
        ))
    })?;
    let receipt = serde_json::json!({
        "candidate": candidate,
        "reason": reason,
    });
    crate::storage::atomic_write(
        &rejected_dir.join(file_name),
        &serde_json::to_vec_pretty(&receipt).expect("json always serializable"),
    )?;
    crate::outbox::remove(path)?;
    Ok(())
}

/// Publishes `agent`'s current local stream tip to `remote` as a single ref
/// update. Reads local state rather than taking a delta from the caller, so
/// it is naturally idempotent and safe to retry: a crash between
/// `drain_outbox` committing locally and the push landing leaves nothing to
/// reconstruct, since the next call simply re-observes the same local tip
/// and re-attempts the same push. A no-op (default/empty receipt) if
/// `agent` has no stream locally yet.
pub fn publish_stream(
    repo: &Path,
    remote: &str,
    agent: &Agent,
) -> AbResult<crate::publish::PublicationReceipt> {
    let tip = match crate::stream::read_stream_tip(repo, agent)? {
        Some(tip) => tip,
        None => return Ok(crate::publish::PublicationReceipt::default()),
    };
    let update =
        crate::publish::RefUpdate::new(crate::stream::stream_ref(agent).into_string(), tip);
    crate::publish::publish(repo, remote, &[update])
}

/// Drains `agent`'s outbox (see [`drain_outbox`]) and then publishes its
/// resulting stream tip to `remote`. Returns both the drain result (what
/// was published, what was rejected and why) and the remote publication
/// receipt; a rejected outbox candidate or a rejected/partial publish
/// receipt is not itself an error (ordinary coordinator policy input, see
/// `drain_outbox`/`publish.rs`) -- inspect the results to learn what
/// actually landed.
#[allow(clippy::too_many_arguments)]
pub fn drain_and_publish(
    repo: &Path,
    git_common_dir: &Path,
    agent: &Agent,
    host: &Short,
    coordinator_custody_epoch: u64,
    worktrees_dir: &Path,
    remote: &str,
) -> AbResult<(DrainResult, crate::publish::PublicationReceipt)> {
    let drained = drain_outbox(
        repo,
        git_common_dir,
        agent,
        host,
        coordinator_custody_epoch,
        worktrees_dir,
    )?;
    let receipt = publish_stream(repo, remote, agent)?;
    Ok((drained, receipt))
}

/// Builds whichever frontier kind `data` requires (docs/AGENT_COORDINATION_
/// EVOLUTION.md section 2.2/4.2, gate 12): a complete frontier -- naming
/// every active member's current position, not just what `extra_refs`
/// names -- for an authority event (currently: a broadcast whose selector
/// is `AllActive`, or a required-ack broadcast on a derived selector, per
/// `apply::broadcast_requires_complete_frontier`), otherwise the ordinary
/// sparse frontier covering exactly the cross-agent identities `extra_refs`
/// names. Same-agent references need no sparse entry (envelope validation
/// follows the stream's own contiguous sequence for those instead).
fn build_frontier(
    repo: &Path,
    epoch: &crate::registry::RosterEpoch,
    worktrees_dir: &Path,
    author: &Agent,
    extra_refs: &[EventId],
    data: &crate::events::EventData,
) -> AbResult<ObservedFrontier> {
    if requires_complete_frontier(data) {
        return build_complete_frontier(repo, epoch, worktrees_dir);
    }
    let mut entries = Vec::new();
    for r in extra_refs {
        let ref_agent = r.agent();
        if ref_agent == *author {
            continue;
        }
        let tip = crate::stream::read_stream_tip(repo, &ref_agent)?.ok_or_else(|| {
            invalid(format!(
                "cannot build a frontier entry for {ref_agent}: it has no stream"
            ))
        })?;
        let _ = worktrees_dir; // reserved: a future version may need to read the referenced stream's own log to validate `r` actually exists there, not just trust the caller.
        entries.push(FrontierEntry {
            agent: ref_agent,
            stream_tip: tip,
            through: r.clone(),
        });
    }
    Ok(ObservedFrontier::sparse(epoch.id.clone(), entries))
}

fn requires_complete_frontier(data: &crate::events::EventData) -> bool {
    match data {
        crate::events::EventData::BroadcastPublished(d) => {
            crate::apply::broadcast_requires_complete_frontier(d)
        }
        _ => false,
    }
}

/// Every active member's current stream position, exactly (`ObservedFrontier
/// ::complete` itself rejects anything short of the epoch's exact active
/// set). Fails if any active member has not yet published its own stream
/// root -- a real, honest failure rather than silently omitting them (which
/// `ObservedFrontier::complete` would reject anyway).
fn build_complete_frontier(
    repo: &Path,
    epoch: &crate::registry::RosterEpoch,
    worktrees_dir: &Path,
) -> AbResult<ObservedFrontier> {
    let mut entries = Vec::new();
    for member in epoch.active_members.keys() {
        let tip = crate::stream::read_stream_tip(repo, member)?.ok_or_else(|| {
            invalid(format!(
                "cannot build a complete frontier: {member} has not yet published its own stream"
            ))
        })?;
        let reads_dir = worktrees_dir.join(format!("_complete_{member}"));
        crate::gitrepo::ensure_bus_worktree(repo, &reads_dir, tip.as_str())?;
        let log_len = crate::storage::read_stream_log(&reads_dir, member)?.len() as u64;
        entries.push(FrontierEntry {
            agent: member.clone(),
            stream_tip: tip,
            through: EventId::new(member, log_len - 1),
        });
    }
    ObservedFrontier::complete(epoch, entries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{AgentStatusEvent, EventData, LifecycleStatus, Role};
    use crate::outbox::Candidate;
    use crate::scalars::{Agent, ObjectId, Text};

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> Text {
        Text::parse(s.to_string()).unwrap()
    }

    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        std::process::Command::new("git")
            .args(["init", "--quiet", "-b", "main"])
            .arg(path)
            .status()
            .unwrap();
        for args in [
            vec!["config", "user.email", "test@example.com"],
            vec!["config", "user.name", "Test"],
        ] {
            std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(args)
                .status()
                .unwrap();
        }
        std::fs::write(path.join("README.md"), "hello\n").unwrap();
        std::process::Command::new("git")
            .arg("-C")
            .arg(path)
            .args(["add", "README.md"])
            .status()
            .unwrap();
        std::process::Command::new("git")
            .arg("-C")
            .arg(path)
            .args(["commit", "-q", "-m", "initial"])
            .status()
            .unwrap();
        dir
    }

    fn init_bare_origin() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        std::process::Command::new("git")
            .args(["init", "--quiet", "--bare", "-b", "main"])
            .arg(dir.path())
            .status()
            .unwrap();
        dir
    }

    fn status_candidate(agent: &Agent, note: &str) -> Candidate {
        let data = EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: text(note),
            product_branch: None,
            product_commit: None,
        });
        Candidate::new(agent, &data, vec![])
    }

    #[test]
    fn drain_outbox_is_a_noop_when_empty() {
        let repo = init_repo();
        let alice = a("alice");
        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();
        assert!(drained.published.is_empty());
        assert!(drained.rejected.is_empty());
    }

    #[test]
    fn drain_outbox_publishes_the_first_event_as_a_stream_root() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        let (_config, epoch, _first_commit) = crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        // A second identity's registration goes through the coordinator,
        // not genesis: it must already be a member of the current epoch
        // for authorize_stream_write to accept it. For this test, add it
        // directly to a fresh epoch via propose_transition (a full
        // registration command that itself proposes the epoch transition
        // is still to come).
        let alice = a("alice");
        let mut members = epoch.active_members.clone();
        members.insert(
            alice.clone(),
            crate::registry::MemberBinding {
                role: Role::Implementor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        crate::registry::propose_transition(
            repo.path(),
            &epoch,
            members,
            &repo.path().join("_transition_wt"),
        )
        .unwrap();

        let candidate = Candidate::new(
            &alice,
            &EventData::AgentRegistered(crate::events::AgentRegistered {
                display_name: short("Alice"),
                primary_role: Role::Implementor,
                purpose: text("x"),
                product_base: None,
                product_branch: None,
                provider: None,
                model: None,
            }),
            vec![],
        );
        crate::outbox::submit(repo.path(), "client-1", &candidate).unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();
        assert_eq!(drained.published.len(), 1);
        assert_eq!(drained.published[0], EventId::new(&alice, 0));
        assert!(drained.rejected.is_empty());
        assert!(crate::stream::read_stream_tip(repo.path(), &alice)
            .unwrap()
            .is_some());
        assert!(crate::outbox::list_pending(repo.path(), &alice)
            .unwrap()
            .is_empty());
    }

    #[test]
    fn drain_outbox_publishes_multiple_pending_candidates_in_one_follow_on_commit() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        crate::outbox::submit(repo.path(), "client-1", &status_candidate(&coord1, "first"))
            .unwrap();
        crate::outbox::submit(
            repo.path(),
            "client-2",
            &status_candidate(&coord1, "second"),
        )
        .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();
        assert_eq!(
            drained.published,
            vec![EventId::new(&coord1, 1), EventId::new(&coord1, 2)]
        );
        assert!(drained.rejected.is_empty());

        let reads_dir = repo.path().join("_reads");
        let (_header, log) = crate::stream::read_stream(repo.path(), &coord1, &reads_dir).unwrap();
        assert_eq!(log.len(), 3); // genesis registration + the two status events
    }

    /// Gate 18, end to end through the real coordinator path: an urgent
    /// candidate submitted *after* an ordinary one still gets the earlier
    /// sequence number and lands first in the published stream --
    /// `list_pending`'s urgent-first ordering (outbox.rs) actually reaches
    /// drain_outbox's sequencing, not just a unit-level property of the
    /// outbox listing in isolation.
    #[test]
    fn drain_outbox_publishes_urgent_candidates_before_ordinary_ones_submitted_earlier() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        crate::outbox::submit(
            repo.path(),
            "ordinary",
            &status_candidate(&coord1, "ordinary, submitted first"),
        )
        .unwrap();
        crate::outbox::submit(
            repo.path(),
            "urgent",
            &status_candidate(&coord1, "urgent, submitted second").urgent(),
        )
        .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();
        assert!(drained.rejected.is_empty());

        let reads_dir = repo.path().join("_reads");
        let (_header, log) = crate::stream::read_stream(repo.path(), &coord1, &reads_dir).unwrap();
        // log[0] is the genesis registration; log[1] must be the urgent
        // candidate despite having been submitted second.
        assert_eq!(log[1].kind, "agent.status");
        assert_eq!(
            log[1].data.get("note").and_then(|v| v.as_str()),
            Some("urgent, submitted second")
        );
        assert_eq!(
            log[2].data.get("note").and_then(|v| v.as_str()),
            Some("ordinary, submitted first")
        );
    }

    /// Adversarial-review regression (Critical): before this fix, nothing
    /// validated a candidate before committing it to the append-only
    /// stream -- a semantically invalid one (e.g. acknowledging an issue
    /// that doesn't exist) would be published unconditionally, and since
    /// `apply::reduce` propagates the first error it hits, that one bad
    /// event would break every future cached/synced read forever, on every
    /// host. Now: an invalid candidate is refused, written to a durable
    /// `rejected/` receipt, removed from the active outbox, and valid
    /// candidates around it still publish normally with a contiguous
    /// sequence (no gap left for the skipped one).
    #[test]
    fn drain_outbox_rejects_an_invalid_candidate_without_blocking_valid_ones() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        let bogus_ack = crate::outbox::Candidate::new(
            &coord1,
            &EventData::IssueAcknowledged(crate::events::IssueAcknowledged {
                issue: EventId::new(&coord1, 99),
                assignment: EventId::new(&coord1, 99),
                note: text(""),
            }),
            vec![],
        );
        crate::outbox::submit(repo.path(), "client-1", &status_candidate(&coord1, "first"))
            .unwrap();
        crate::outbox::submit(repo.path(), "client-2", &bogus_ack).unwrap();
        crate::outbox::submit(repo.path(), "client-3", &status_candidate(&coord1, "third"))
            .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();

        // Both valid candidates publish with a contiguous sequence -- no
        // gap left for the rejected one in between.
        assert_eq!(
            drained.published,
            vec![EventId::new(&coord1, 1), EventId::new(&coord1, 2)]
        );
        assert_eq!(drained.rejected.len(), 1);
        assert_eq!(drained.rejected[0].kind, "issue.acknowledged");
        assert!(
            drained.rejected[0].reason.contains("unknown issue"),
            "{}",
            drained.rejected[0].reason
        );

        // Nothing left pending, and the rejected candidate's own outbox
        // entry is gone (not stuck retrying forever) but durably recorded.
        assert!(crate::outbox::list_pending(repo.path(), &coord1)
            .unwrap()
            .is_empty());
        let rejected_dir = crate::outbox::outbox_dir(repo.path(), &coord1).join("rejected");
        let entries: Vec<_> = std::fs::read_dir(&rejected_dir).unwrap().collect();
        assert_eq!(entries.len(), 1);

        // The stream itself is clean: reduce() must not choke on anything
        // that was never actually published.
        let snap = crate::sync::cached_snapshot(repo.path(), &repo.path().join("_snap")).unwrap();
        assert_eq!(snap.state.agents[&coord1].next_seq, 3);
    }

    #[test]
    fn drain_outbox_rejects_an_agent_not_in_the_current_epoch() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        let mallory = a("mallory");
        crate::outbox::submit(repo.path(), "client-1", &status_candidate(&mallory, "hi")).unwrap();
        let err = drain_outbox(
            repo.path(),
            repo.path(),
            &mallory,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("not an active member"), "{err}");
    }

    #[test]
    fn publish_stream_is_a_noop_when_the_agent_has_no_local_stream() {
        let repo = init_repo();
        let origin = init_bare_origin();
        let alice = a("alice");
        let receipt =
            publish_stream(repo.path(), &origin.path().to_string_lossy(), &alice).unwrap();
        assert_eq!(receipt, crate::publish::PublicationReceipt::default());
    }

    #[test]
    fn publish_stream_pushes_an_already_committed_local_tip() {
        let repo = init_repo();
        let origin = init_bare_origin();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        let local_tip = crate::stream::read_stream_tip(repo.path(), &coord1)
            .unwrap()
            .unwrap();
        let receipt =
            publish_stream(repo.path(), &origin.path().to_string_lossy(), &coord1).unwrap();
        assert_eq!(
            receipt.published.get("refs/heads/agent-events/coord1"),
            Some(&local_tip)
        );
        assert_eq!(
            crate::gitrepo::rev_parse(origin.path(), "refs/heads/agent-events/coord1").unwrap(),
            local_tip.into_string()
        );
    }

    #[test]
    fn drain_and_publish_pushes_the_new_tip_to_the_remote() {
        let repo = init_repo();
        let origin = init_bare_origin();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();
        crate::outbox::submit(repo.path(), "client-1", &status_candidate(&coord1, "hi")).unwrap();

        let (drained, receipt) = drain_and_publish(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
            &origin.path().to_string_lossy(),
        )
        .unwrap();
        assert_eq!(drained.published, vec![EventId::new(&coord1, 1)]);
        assert!(drained.rejected.is_empty());

        let local_tip = crate::stream::read_stream_tip(repo.path(), &coord1)
            .unwrap()
            .unwrap();
        assert_eq!(
            receipt.published.get("refs/heads/agent-events/coord1"),
            Some(&local_tip)
        );
        assert_eq!(
            crate::gitrepo::rev_parse(origin.path(), "refs/heads/agent-events/coord1").unwrap(),
            local_tip.into_string()
        );
    }

    #[test]
    fn drain_and_publish_is_a_noop_when_the_outbox_is_empty() {
        let repo = init_repo();
        let origin = init_bare_origin();
        let alice = a("alice");
        let (drained, receipt) = drain_and_publish(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
            &origin.path().to_string_lossy(),
        )
        .unwrap();
        assert!(drained.published.is_empty());
        assert!(drained.rejected.is_empty());
        assert_eq!(receipt, crate::publish::PublicationReceipt::default());
    }

    /// End-to-end proof that `build_frontier` can actually construct a
    /// complete frontier (not just that `apply.rs` correctly rejects a
    /// sparse one): an `AllActive` broadcast, submitted through the
    /// ordinary outbox and drained through the real coordinator path
    /// (not a hand-built `Envelope`), must publish successfully.
    #[test]
    fn drain_outbox_publishes_an_all_active_broadcast_with_a_real_complete_frontier() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        let (_config, epoch, _commit) = crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        let alice = a("alice");
        let mut members = epoch.active_members.clone();
        members.insert(
            alice.clone(),
            crate::registry::MemberBinding {
                role: Role::Implementor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        let new_epoch = crate::registry::propose_transition(
            repo.path(),
            &epoch,
            members,
            &repo.path().join("_transition_wt"),
        )
        .unwrap();
        crate::outbox::submit(
            repo.path(),
            "alice-reg",
            &Candidate::new(
                &alice,
                &EventData::AgentRegistered(crate::events::AgentRegistered {
                    display_name: short("Alice"),
                    primary_role: Role::Implementor,
                    purpose: text("x"),
                    product_base: None,
                    product_branch: None,
                    provider: None,
                    model: None,
                }),
                vec![],
            ),
        )
        .unwrap();
        drain_outbox(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt_alice"),
        )
        .unwrap();

        let broadcast_data = EventData::BroadcastPublished(crate::events::BroadcastPublished {
            topics: crate::scalars::StringSet::from_iter([
                crate::scalars::CoordinationTopic::parse("release.main".into()).unwrap(),
            ]),
            importance: crate::common::Importance::Informational,
            summary: short("s"),
            detail: text("d"),
            affected_paths: crate::scalars::StringSet::default(),
            affected_interfaces: crate::scalars::StringSet::default(),
            product_commits: crate::scalars::StringSet::default(),
            audience_selector: crate::common::AudienceSelector::AllActive,
            audience_epoch: new_epoch.id.clone(),
            audience_snapshot: crate::scalars::StringSet::from_iter([
                alice.clone(),
                coord1.clone(),
            ]),
            acknowledgement: crate::common::AckRequirement::None,
            deadline: None,
            supersedes: crate::scalars::StringSet::default(),
            workaround: None,
            expiry_condition: None,
        });
        crate::outbox::submit(
            repo.path(),
            "broadcast-1",
            &Candidate::new(&coord1, &broadcast_data, vec![]),
        )
        .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt_coord1"),
        )
        .unwrap();
        assert!(
            drained.rejected.is_empty(),
            "broadcast was rejected: {:?}",
            drained.rejected
        );
        assert_eq!(drained.published.len(), 1);
    }
}
