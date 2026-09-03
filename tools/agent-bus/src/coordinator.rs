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
use crate::error::{invalid, AbResult};
use crate::frontier::{FrontierEntry, ObservedFrontier};
use crate::scalars::{Agent, EventId, Short};
use std::path::Path;

/// Drains every pending candidate in `agent`'s local outbox, in submission
/// order, and publishes them as one or two new stream commits (a root
/// commit if this is the agent's first-ever event, then a follow-on commit
/// for the rest). Returns the published `EventId`s. An empty outbox is a
/// no-op returning `Ok(vec![])`.
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
) -> AbResult<Vec<EventId>> {
    let pending = crate::outbox::list_pending(git_common_dir, agent)?;
    if pending.is_empty() {
        return Ok(vec![]);
    }

    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists yet"))?;
    let epoch = crate::registry::read_epoch(repo, &registry_tip, &worktrees_dir.join("_epoch"))?;
    crate::registry::authorize_stream_write(&epoch, agent, host, coordinator_custody_epoch)?;

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
    for (path, candidate) in &pending {
        let data = candidate.typed_data()?;
        let observed = build_frontier(repo, &epoch, &worktrees_dir.join("_frontier"), agent, &candidate.extra_refs)?;
        let env = Envelope::new(agent, next_seq, observed, &data, candidate.extra_refs.clone());
        envelopes.push((path.clone(), env));
        next_seq += 1;
    }

    let mut published = Vec::with_capacity(envelopes.len());
    let mut remaining: Vec<Envelope> = envelopes.iter().map(|(_, e)| e.clone()).collect();
    let mut new_tip = existing_tip;

    if new_tip.is_none() {
        let first = remaining.remove(0);
        let header = crate::stream::StreamHeader {
            agent: agent.clone(),
            activation_event: None,
            registration_authority: first.id.clone(),
            final_v1_seq: None,
            object_format: "sha1".to_string(),
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

    Ok(published)
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
    let update = crate::publish::RefUpdate::new(crate::stream::stream_ref(agent).into_string(), tip);
    crate::publish::publish(repo, remote, &[update])
}

/// Drains `agent`'s outbox (see [`drain_outbox`]) and then publishes its
/// resulting stream tip to `remote`. Returns both the newly published
/// `EventId`s and the remote publication receipt; a rejected or partial
/// receipt is not itself an error (ordinary coordinator policy input, see
/// `publish.rs`) -- inspect the receipt to learn what actually landed.
#[allow(clippy::too_many_arguments)]
pub fn drain_and_publish(
    repo: &Path,
    git_common_dir: &Path,
    agent: &Agent,
    host: &Short,
    coordinator_custody_epoch: u64,
    worktrees_dir: &Path,
    remote: &str,
) -> AbResult<(Vec<EventId>, crate::publish::PublicationReceipt)> {
    let published = drain_outbox(
        repo,
        git_common_dir,
        agent,
        host,
        coordinator_custody_epoch,
        worktrees_dir,
    )?;
    let receipt = publish_stream(repo, remote, agent)?;
    Ok((published, receipt))
}

/// Builds a sparse frontier covering exactly the cross-agent identities
/// `extra_refs` names, each pinned at that referenced event's own position
/// against the referenced agent's *current* stream tip. Same-agent
/// references need no frontier entry (envelope validation follows the
/// stream's own contiguous sequence for those instead).
fn build_frontier(
    repo: &Path,
    epoch: &crate::registry::RosterEpoch,
    worktrees_dir: &Path,
    author: &Agent,
    extra_refs: &[EventId],
) -> AbResult<ObservedFrontier> {
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
        let published = drain_outbox(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();
        assert!(published.is_empty());
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
            },
        );
        crate::registry::propose_transition(repo.path(), &epoch, members, &repo.path().join("_transition_wt"))
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

        let published = drain_outbox(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();
        assert_eq!(published.len(), 1);
        assert_eq!(published[0], EventId::new(&alice, 0));
        assert_eq!(
            crate::stream::read_stream_tip(repo.path(), &alice).unwrap().is_some(),
            true
        );
        assert!(crate::outbox::list_pending(repo.path(), &alice).unwrap().is_empty());
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

        crate::outbox::submit(
            repo.path(),
            "client-1",
            &status_candidate(&coord1, "first"),
        )
        .unwrap();
        crate::outbox::submit(
            repo.path(),
            "client-2",
            &status_candidate(&coord1, "second"),
        )
        .unwrap();

        let published = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
        )
        .unwrap();
        assert_eq!(published, vec![EventId::new(&coord1, 1), EventId::new(&coord1, 2)]);

        let reads_dir = repo.path().join("_reads");
        let (_header, log) = crate::stream::read_stream(repo.path(), &coord1, &reads_dir).unwrap();
        assert_eq!(log.len(), 3); // genesis registration + the two status events
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
        let receipt = publish_stream(
            repo.path(),
            &origin.path().to_string_lossy(),
            &alice,
        )
        .unwrap();
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
        let receipt = publish_stream(
            repo.path(),
            &origin.path().to_string_lossy(),
            &coord1,
        )
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

        let (published, receipt) = drain_and_publish(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
            &origin.path().to_string_lossy(),
        )
        .unwrap();
        assert_eq!(published, vec![EventId::new(&coord1, 1)]);

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
        let (published, receipt) = drain_and_publish(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
            &origin.path().to_string_lossy(),
        )
        .unwrap();
        assert!(published.is_empty());
        assert_eq!(receipt, crate::publish::PublicationReceipt::default());
    }
}
