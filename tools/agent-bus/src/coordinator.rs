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
/// This validates against what is already *locally* known by default, not a
/// fresh remote probe -- ordinarily a real, disclosed limitation: a
/// candidate that is actually valid but looks invalid only because this
/// host's local view is stale will be rejected and must be resubmitted,
/// rather than the coordinator silently fetching first. Gate 17 carves out
/// an exception for currency-sensitive kinds (`requires_synced_snapshot`:
/// merge authorization, schema/merge-engine activation, an all-active or
/// required-ack broadcast audience, or a reassignment) -- for those, this
/// function fetches from `remote` first and validates the *entire* batch
/// against that freshly-synced state (a fresher view never hurts an
/// ordinary candidate either), and fails any currency-sensitive candidate
/// closed with the fetch's own error if that fetch itself fails, rather
/// than silently falling back to a stale cached cut for just those.
///
/// `host`/`coordinator_custody_epoch` identify the caller's own claimed
/// custody, checked against the current registry epoch before anything is
/// written (gate 6/7's precondition, via `registry::authorize_stream_write`).
#[allow(clippy::too_many_arguments)]
pub fn drain_outbox(
    repo: &Path,
    git_common_dir: &Path,
    agent: &Agent,
    host: &Short,
    coordinator_custody_epoch: u64,
    worktrees_dir: &Path,
    remote: &str,
) -> AbResult<DrainResult> {
    let pending = crate::outbox::list_pending(git_common_dir, agent)?;
    if pending.is_empty() {
        return Ok(DrainResult::default());
    }

    // Fetch first, before reading anything else, when the batch needs it --
    // so `epoch` below (and `state`) reflect the same freshly-synced cut
    // consistently, rather than mixing a fresh `state` with a registry
    // epoch read moments earlier from a possibly-older local tip.
    let needs_fresh = pending
        .iter()
        .any(|(_, c)| c.typed_data().is_ok_and(|d| requires_synced_snapshot(&d)));
    let mut fresh_sync_err: Option<String> = None;
    let mut fresh_state = None;
    if needs_fresh {
        match crate::sync::synced_snapshot(
            repo,
            git_common_dir,
            remote,
            &worktrees_dir.join("_validate_synced"),
        ) {
            Ok(snap) => fresh_state = Some(snap.state),
            Err(e) => fresh_sync_err = Some(e.to_string()),
        }
    }

    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists yet"))?;
    let epoch = crate::registry::read_epoch(repo, &registry_tip, &worktrees_dir.join("_epoch"))?;
    crate::registry::authorize_stream_write(&epoch, agent, host, coordinator_custody_epoch)?;

    let mut state = match fresh_state {
        Some(s) => s,
        None => {
            crate::sync::cached_snapshot(repo, git_common_dir, &worktrees_dir.join("_validate"))?
                .state
        }
    };

    let existing_tip = crate::stream::read_stream_tip(repo, agent)?;
    let mut next_seq = if let Some(tip) = &existing_tip {
        let reads_dir = worktrees_dir.join(format!("_read_{agent}"));
        crate::storage::read_stream_log(
            &{
                crate::gitrepo::ensure_bus_worktree(repo, &reads_dir, tip.as_str())?;
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
        // Gate 17: fail closed rather than validate a currency-sensitive
        // candidate against a stale cached cut just because the fresh probe
        // above failed -- reject it outright, with the fetch's own error,
        // instead of silently falling back the way an ordinary candidate
        // does.
        if let Some(fetch_err) = &fresh_sync_err {
            if requires_synced_snapshot(&data) {
                let reason = format!(
                    "requires a current-as-of-remote-probe view (gate 17) but the fetch failed: \
                     {fetch_err}"
                );
                reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
                rejected.push(RejectedCandidate {
                    kind: candidate.kind.clone(),
                    reason,
                });
                continue;
            }
        }
        // AGENT_REVIEW.md section 7/`apply.rs`'s own module doc: `apply::
        // dry_run` (below) never touches git, so it cannot confirm a
        // `review.merge_authorized` candidate's `candidate` is the real
        // deterministic reconstruction of `previous_main`/`reviewed_commit`/
        // reviewer, that every introduced commit actually carries the right
        // `Agent-Bus-Agent` trailers, or that the candidate tag proving a
        // conflict-free merge was ever published anywhere another agent
        // could see. Nothing stops a hand-crafted `submit --kind review.
        // merge_authorized` from skipping `cli::prepare_merge` entirely and
        // asserting all of that -- so re-run it here, at the actual
        // publication gate, exactly like gate 17 (reject via a durable
        // receipt, never `?`-propagate past this one candidate).
        if let crate::events::EventData::ReviewMergeAuthorized(d) = &data {
            if let Err(e) = verify_review_merge_authorized(repo, remote, &state, agent, d) {
                let reason = e.to_string();
                reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
                rejected.push(RejectedCandidate {
                    kind: candidate.kind.clone(),
                    reason,
                });
                continue;
            }
        }
        // AGENT_REVIEW.md section 11/`apply.rs`'s own module doc: `apply::
        // apply_review_merge_reconciled` only checks that the submitted
        // values equal the named authorization -- it never touches git, so
        // it cannot confirm the recovery receipt's own precondition ("only
        // after checking the authorized candidate is already the
        // corresponding first-parent `main` commit"). Nothing stops a
        // hand-crafted `submit --kind review.merge_reconciled` from
        // asserting that regardless of what real `main` history actually
        // says -- re-run it here, at the actual publication gate, exactly
        // like the identical `review.merge_authorized` gate just above (see
        // `verify_review_merge_reconciled`'s own doc comment).
        if let crate::events::EventData::ReviewMergeReconciled(d) = &data {
            if let Err(e) = verify_review_merge_reconciled(repo, &state, d) {
                let reason = e.to_string();
                reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
                rejected.push(RejectedCandidate {
                    kind: candidate.kind.clone(),
                    reason,
                });
                continue;
            }
        }
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
        remote,
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
/// sparse frontier covering every cross-agent identity `data` itself
/// references (`EventData::referenced_ids()`) unioned with whatever
/// `extra_refs` additionally names. Same-agent references need no sparse
/// entry (envelope validation follows the stream's own contiguous sequence
/// for those instead).
///
/// Deliberately derived from `data.referenced_ids()`, not just `extra_refs`
/// (the CLI's `--observes` list) alone: `Envelope::new` sets the resulting
/// envelope's `refs` field to `data.referenced_ids() ∪ extra_refs`
/// (envelope.rs), and gate 4 (`ObservedFrontier::validate_reference`)
/// requires every cross-agent id in `refs` to already have frontier
/// coverage. Building coverage from `extra_refs` alone left that entirely
/// up to the caller remembering to pass `--observes` for every
/// payload-referenced id even when the payload already names it plainly
/// (e.g. `ReviewNominationAccepted.nomination`) -- an easy, non-adversarial
/// operator mistake, not a malicious one. Missing it here doesn't merely
/// fail this one submission: `apply_event`'s own gate-4 recheck (added
/// alongside this fix) would still catch the resulting self-inconsistent
/// envelope, but only in `dry_run`, i.e. only for submissions that go
/// through this function in the first place -- so fixing the frontier's own
/// construction is the real, source-level fix (round-5 adversarial review,
/// reproduced live across two checkouts: omitting `--observes` for a plain
/// `review.nomination_accepted` durably corrupted that stream fleet-wide,
/// since nothing at write time re-checked what `Envelope::parse_line`
/// enforces at read time).
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
    // One entry per cross-agent identity referenced, `through` set to the
    // *furthest* seq referenced for that agent (so gate 4 accepts every
    // reference to it, not just the last one considered).
    let mut through: std::collections::BTreeMap<Agent, EventId> = std::collections::BTreeMap::new();
    for r in data.referenced_ids().iter().chain(extra_refs.iter()) {
        let ref_agent = r.agent();
        if ref_agent == *author {
            continue;
        }
        through
            .entry(ref_agent)
            .and_modify(|existing| {
                if r.seq() > existing.seq() {
                    *existing = r.clone();
                }
            })
            .or_insert_with(|| r.clone());
    }
    let mut entries = Vec::with_capacity(through.len());
    for (ref_agent, r) in through {
        let tip = crate::stream::read_stream_tip(repo, &ref_agent)?.ok_or_else(|| {
            invalid(format!(
                "cannot build a frontier entry for {ref_agent}: it has no stream"
            ))
        })?;
        let _ = worktrees_dir; // reserved: a future version may need to read the referenced stream's own log to validate `r` actually exists there, not just trust the caller.
        entries.push(FrontierEntry {
            agent: ref_agent,
            stream_tip: tip,
            through: r,
        });
    }
    Ok(ObservedFrontier::sparse(epoch.id.clone(), entries))
}

/// The git-linked half of `review.merge_authorized` validation
/// (AGENT_REVIEW.md section 7) that `apply.rs` deliberately leaves out of
/// its pure, git-repo-free reduction. Re-runs `merge_candidate::verify_
/// authorship`/`reconstruct_candidate` against the *submitted* payload
/// (`d`) -- not merely trusting that `cli::prepare_merge` was ever run, or
/// run honestly -- and confirms the candidate tag `prepare-merge` would
/// have published is independently fetchable from `remote`
/// (`gitrepo::remote_tag_matches`, a real `ls-remote`). Deliberately does
/// *not* additionally require the tag to already exist in this checkout's
/// own local clone: `drain_outbox` may run from any checkout, not just the
/// one that ran `prepare-merge`, and a tag genuinely pushed from elsewhere
/// is valid here even though this checkout has never fetched it.
///
/// `Ok(())` when `d.nomination` does not resolve in `state` at all: that is
/// an ordinary, unrelated validation failure `apply::dry_run` reports
/// moments later with a clearer, nomination-specific message, so it is not
/// duplicated here. Likewise `Ok(())` when `d.nomination` names a nomination
/// link the chain has since moved past (`chain.current_nomination !=
/// d.nomination`) -- `apply::apply_review_merge_authorized`'s own identical
/// branch treats that as a harmless, already-inapplicable no-op rather than
/// a hard failure, and this gate defers to that same semantics rather than
/// rejecting a stale-but-otherwise-harmless authorization on a technicality.
fn verify_review_merge_authorized(
    repo: &Path,
    remote: &str,
    state: &crate::state::BusState,
    reviewer: &Agent,
    d: &crate::events::ReviewMergeAuthorized,
) -> AbResult<()> {
    let chain = match state.review_chain(&d.nomination) {
        Some(c) => c,
        None => return Ok(()),
    };
    if chain.current_nomination != d.nomination {
        return Ok(());
    }
    let expected_authors: std::collections::BTreeSet<Agent> =
        chain.current_request.authors.iter().cloned().collect();
    crate::merge_candidate::verify_authorship(
        repo,
        reviewer,
        &expected_authors,
        d.previous_main.as_str(),
        d.reviewed_commit.as_str(),
    )?;
    let reconstructed = crate::merge_candidate::reconstruct_candidate(
        repo,
        d.previous_main.as_str(),
        d.reviewed_commit.as_str(),
        reviewer,
    )?;
    if reconstructed != d.candidate.as_str() {
        return Err(invalid(format!(
            "candidate {} does not match the deterministic reconstruction {reconstructed} from \
             previous_main/reviewed_commit/reviewer",
            d.candidate
        )));
    }
    // Deliberately no local-only `tag_exists_at` precondition here: `drain_outbox`
    // may run from any checkout, not just the one `prepare-merge` ran from, and a
    // tag `prepare-merge` pushed from a *different* checkout is genuinely valid
    // even though this checkout has never fetched it. `remote_tag_matches` (a real
    // `ls-remote`) is the checkout-independent, authoritative check for "other
    // agents could verify this merge" -- see its own doc comment -- so it alone is
    // both necessary and sufficient here.
    let tag = crate::merge_candidate::candidate_tag_name(reviewer, d.candidate.as_str());
    if !crate::gitrepo::remote_tag_matches(repo, remote, &tag, d.candidate.as_str())? {
        return Err(invalid(format!(
            "candidate tag refs/tags/{tag} is not fetchable from {remote}; other agents could \
             not verify this merge"
        )));
    }
    Ok(())
}

/// The git-linked half of `review.merge_reconciled` validation
/// (AGENT_REVIEW.md section 11) that `apply.rs` deliberately leaves out of
/// its pure, git-repo-free reduction -- see `apply.rs`'s own module doc, and
/// `apply::apply_review_merge_reconciled`'s own field-equality-only checks
/// against the named authorization. Section 11: a bootstrap-authorized
/// coordinator "emits `review.merge_reconciled` only after checking the
/// authorized candidate is already the corresponding first-parent `main`
/// commit" -- exactly the live-Git fact this function checks, ported from
/// the shipped version-one helper's `review_cmds::reconcile` (`rev_list_
/// first_parent(previous_main, refs/heads/main)` containing `main_commit`),
/// mirroring `verify_review_merge_authorized`'s identical reasoning for why
/// this cannot live in `apply.rs` and cannot be skipped just because `cli::
/// reconcile` doesn't exist: unlike `review.merge_authorized`/`merge-ready`
/// (which have dedicated `prepare-merge`/`merge-ready` CLI commands because
/// they *construct* or *pre-flight-check* a candidate), `review.merge_
/// reconciled` is published through the ordinary generic `submit --kind
/// review.merge_reconciled` path (see `cli.rs`'s module doc on the commands
/// it does and does not special-case) -- so this gate, not a dedicated CLI
/// wrapper, is the only place that can ever re-derive this fact from real
/// git history before the event is durably published.
///
/// `Ok(())` when `d.authorization` does not resolve to a `review.merge_
/// authorized` event in `state` at all (an unknown/wrong-kind authorization
/// id): that is an ordinary, unrelated validation failure `apply::dry_run`
/// reports moments later via `apply_review_merge_reconciled`'s own clearer,
/// authorization-specific message, so it is not duplicated here.
fn verify_review_merge_reconciled(
    repo: &Path,
    state: &crate::state::BusState,
    d: &crate::events::ReviewMergeReconciled,
) -> AbResult<()> {
    let Some(auth_env) = state.events.get(&d.authorization) else {
        return Ok(());
    };
    match auth_env.typed_data() {
        Ok(crate::events::EventData::ReviewMergeAuthorized(_)) => {}
        _ => return Ok(()),
    }
    let is_first_parent_of_main =
        crate::gitrepo::rev_list_first_parent(repo, d.previous_main.as_str(), "refs/heads/main")?
            .iter()
            .any(|c| c == d.main_commit.as_str());
    if !is_first_parent_of_main {
        return Err(invalid(format!(
            "main_commit {} is not a first-parent successor of previous_main {} on current \
             main -- reconcile only records a merge that has genuinely already landed",
            d.main_commit, d.previous_main
        )));
    }
    Ok(())
}

fn requires_complete_frontier(data: &crate::events::EventData) -> bool {
    match data {
        crate::events::EventData::BroadcastPublished(d) => {
            crate::apply::broadcast_requires_complete_frontier(d)
        }
        // Section 2.2: "events that grant merge authority... activate
        // schemas... or make another fleet-wide decision use a complete
        // frontier" -- merge_engine.activated is exactly the latter, a
        // fleet-wide pinned-engine change (see apply::require_complete_
        // frontier, called by all three of these handlers).
        crate::events::EventData::SchemaActivated(_)
        | crate::events::EventData::MergeEngineActivated(_)
        | crate::events::EventData::ReviewMergeAuthorized(_) => true,
        _ => false,
    }
}

/// Gate 17 (AGENT_COORDINATION_EVOLUTION.md section 2.4): "merge readiness,
/// reassignment, schema activation, all-active audience construction...
/// require a current-as-of-remote-probe receipt and fail closed rather than
/// silently using a cached cut." Every complete-frontier kind already
/// qualifies (merge authorization, schema/merge-engine activation, an
/// all-active or required-ack broadcast audience) since a stale local view
/// could under-report the active set or the currently selected epoch;
/// reassignment additionally qualifies even though it needs only a sparse
/// frontier, since validating it against a stale cached view of the
/// existing assignment can accept a reassignment that is actually already
/// stale -- the identical failure mode a fresh cut is meant to close, just
/// on a different validation path.
fn requires_synced_snapshot(data: &crate::events::EventData) -> bool {
    use crate::events::EventData;
    requires_complete_frontier(data)
        || matches!(
            data,
            EventData::IssueReassigned(_)
                | EventData::DependencyReassigned(_)
                | EventData::ReviewReassigned(_)
        )
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
            "origin",
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
            "origin",
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
            "origin",
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
            "origin",
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
            "origin",
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
        let snap =
            crate::sync::cached_snapshot(repo.path(), repo.path(), &repo.path().join("_snap"))
                .unwrap();
        assert_eq!(snap.state.agents[&coord1].next_seq, 3);
    }

    /// Gate 17 (AGENT_COORDINATION_EVOLUTION.md section 2.4): a
    /// currency-sensitive candidate (here, `schema.activated`) must be
    /// refused, not validated against a stale cached cut, when the fresh
    /// remote probe itself fails -- while an ordinary candidate in the same
    /// batch is unaffected, since only the currency-sensitive one actually
    /// needs that fresher view.
    #[test]
    fn drain_outbox_fails_closed_on_a_currency_sensitive_candidate_when_the_fetch_fails() {
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

        crate::outbox::submit(repo.path(), "ordinary", &status_candidate(&coord1, "hi")).unwrap();
        let schema_activate = crate::outbox::Candidate::new(
            &coord1,
            &EventData::SchemaActivated(crate::events::SchemaActivated {
                version: 2,
                design_commit: ObjectId::parse("a".repeat(40)).unwrap(),
                helper_commit: ObjectId::parse("b".repeat(40)).unwrap(),
            }),
            vec![],
        );
        crate::outbox::submit(repo.path(), "schema", &schema_activate).unwrap();

        // No "origin" remote exists in this repo at all, so the gate-17
        // fetch is guaranteed to fail.
        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt"),
            "origin",
        )
        .unwrap();

        assert_eq!(drained.published, vec![EventId::new(&coord1, 1)]);
        assert_eq!(drained.rejected.len(), 1);
        assert_eq!(drained.rejected[0].kind, "schema.activated");
        assert!(
            drained.rejected[0].reason.contains("gate 17"),
            "{}",
            drained.rejected[0].reason
        );
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
            "origin",
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
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();
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
            &remote,
        )
        .unwrap();

        // Gate 17: constructing a complete/all-active frontier is
        // currency-sensitive, so `drain_outbox` below will fetch `remote`
        // first -- push everything built so far (the registry transition
        // and both agents' streams) there now, exactly as a real
        // coordinator would before authorizing something currency
        // -sensitive.
        let coord1_tip = crate::stream::read_stream_tip(repo.path(), &coord1)
            .unwrap()
            .unwrap();
        let alice_tip = crate::stream::read_stream_tip(repo.path(), &alice)
            .unwrap()
            .unwrap();
        crate::publish::publish(
            repo.path(),
            &remote,
            &[
                crate::publish::RefUpdate::new(crate::registry::REGISTRY_REF, new_epoch.id.clone()),
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&coord1).into_string(),
                    coord1_tip,
                ),
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&alice).into_string(),
                    alice_tip,
                ),
            ],
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
            &remote,
        )
        .unwrap();
        assert!(
            drained.rejected.is_empty(),
            "broadcast was rejected: {:?}",
            drained.rejected
        );
        assert_eq!(drained.published.len(), 1);
    }

    /// Round-5 adversarial review, reproduced live: a sparse-frontier
    /// event's author omits `--observes` for a cross-agent id their own
    /// payload already names (a plausible, non-adversarial operator
    /// mistake -- there is no dedicated `issue take`/`review accept`
    /// command, only generic `submit`). Before this fix, `build_frontier`
    /// only covered `extra_refs` (`--observes`), so the resulting envelope's
    /// `refs` (derived by `Envelope::new` from `data.referenced_ids()`)
    /// named an agent the envelope's own `observed` frontier didn't cover
    /// -- `apply::dry_run` never caught it (no gate-4 recheck existed), so
    /// it committed and published, and then permanently failed to reduce
    /// on *any* checkout (including this one, on its next cold read) via
    /// `Envelope::parse_line`'s stricter gate-4 check. Proves both halves
    /// of the fix at once: `drain_outbox` accepts the omitted-`--observes`
    /// submission (frontier auto-derived from the payload), and the
    /// resulting committed stream survives a full independent re-read
    /// through `stream::read_stream` (which round-trips every line through
    /// `parse_line`) -- i.e. it does not corrupt itself.
    #[test]
    fn drain_outbox_auto_derives_frontier_coverage_for_a_cross_agent_reference_missing_observes() {
        let repo = init_repo();
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();
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
        crate::registry::propose_transition(
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
            &remote,
        )
        .unwrap();

        let issue_data = EventData::IssueOpened(crate::events::IssueOpened {
            target: alice.clone(),
            issue_kind: crate::events::IssueKind::Bug,
            severity: crate::common::Priority::Normal,
            summary: text("s"),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks: crate::scalars::StringSet::default(),
            evidence: crate::scalars::StringSet::default(),
        });
        crate::outbox::submit(
            repo.path(),
            "issue-1",
            &Candidate::new(&coord1, &issue_data, vec![]),
        )
        .unwrap();
        let issue_drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &repo.path().join("_wt_coord1"),
            &remote,
        )
        .unwrap();
        assert!(
            issue_drained.rejected.is_empty(),
            "{:?}",
            issue_drained.rejected
        );
        let issue_id = issue_drained.published[0].clone();

        // The bug trigger: alice acknowledges coord1's issue but the
        // candidate carries no `extra_refs` at all -- exactly what a plain
        // `submit` with no `--observes` flag produces.
        let ack_data = EventData::IssueAcknowledged(crate::events::IssueAcknowledged {
            issue: issue_id.clone(),
            assignment: issue_id.clone(),
            note: text("on it"),
        });
        crate::outbox::submit(
            repo.path(),
            "ack-1",
            &Candidate::new(&alice, &ack_data, vec![]),
        )
        .unwrap();
        let ack_drained = drain_outbox(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            &repo.path().join("_wt_alice_ack"),
            &remote,
        )
        .unwrap();
        assert!(
            ack_drained.rejected.is_empty(),
            "cross-agent reference should have been auto-covered by build_frontier: {:?}",
            ack_drained.rejected
        );
        assert_eq!(ack_drained.published.len(), 1);

        // And the committed stream survives a full independent re-read --
        // every line round-trips through `Envelope::parse_line`'s own
        // gate-4 check, proving the envelope actually written to disk is
        // self-consistent, not merely that `dry_run` was fooled the same
        // way twice.
        let (_header, log) =
            crate::stream::read_stream(repo.path(), &alice, &repo.path().join("_reread_alice"))
                .unwrap();
        assert_eq!(log.len(), 2); // registration + acknowledgement
    }

    // ---------------------------------------------------------------
    // `review.merge_authorized`'s git-linked gate (AGENT_REVIEW.md section
    // 7; see `verify_review_merge_authorized`'s own doc comment). Mirrors
    // the shipped version-one helper's `review_cmds.rs` falsifying test
    // list (`authorize_rejects_*`, `prepare_merge_fails_when_candidate_tag_
    // push_to_origin_fails`, `authorize_rejects_candidate_tag_that_never_
    // reached_origin`) against v2's real coordinator path instead of a v1
    // `BusCtx`.

    fn git(dir: &Path, args: &[&str]) -> String {
        let out = std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "git {args:?} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    }

    /// A real repo with `coord1` (coordinator), `zoe` (implementor/author),
    /// and `aiden` (reviewer) all registered and already pushed to a real
    /// bare `origin` -- required because `review.merge_authorized` always
    /// needs gate 17's complete-frontier fetch to succeed (`requires_
    /// complete_frontier` names it unconditionally) before `verify_review_
    /// merge_authorized` is ever reached, so every test below needs a
    /// reachable, up-to-date remote regardless of what it is separately
    /// testing. Also builds one real `feature.txt` commit on top of `main`,
    /// authored by `trailer_agent` via an `Agent-Bus-Agent` trailer (`None`
    /// omits the trailer entirely, for the "missing trailer" fixture), plus
    /// an accepted `review.nominated`/`review.nomination_accepted` pair
    /// naming `aiden` as reviewer and `zoe` as the nomination's sole author
    /// -- mirrors v1's `review_cmds::build_fixture`.
    ///
    /// The reviewer's name ("aiden") happening to sort before the author's
    /// ("zoe") is cosmetic, not load-bearing: `topological_order`'s ready-set
    /// tie-break always prefers *any* remaining `seq == 0` event (an agent's
    /// own registration, which has zero dependencies and so is ready from
    /// the very start of a cold reduce) over *any* `seq > 0` event,
    /// regardless of which agent it belongs to or how names compare --
    /// see its own doc comment. A registration can therefore never be
    /// starved out by an event that merely *names* that agent (e.g.
    /// `review.nominated`'s `reviewer` field, a bare `Agent` identity, not
    /// an `EventId`, so invisible to the dependency graph itself). Verified
    /// directly: swapping this fixture's names so the reviewer sorts *after*
    /// the author (e.g. "bob"/"alice") reproduces no failure, through the
    /// full nominate/accept/prepare-merge sequence, both via this fixture
    /// and via the real CLI end to end.
    struct ReviewFixture {
        repo: tempfile::TempDir,
        #[allow(dead_code)]
        origin: tempfile::TempDir,
        remote: String,
        coord1: Agent,
        author: Agent,
        reviewer: Agent,
        nomination: EventId,
        feature_commit: String,
        previous_main: String,
    }

    fn build_review_fixture(trailer_agent: Option<&str>) -> ReviewFixture {
        use crate::events::{
            AgentRegistered, EventData, ReviewNominated, ReviewNominationAccepted,
        };
        use crate::registry::MemberBinding;
        use crate::scalars::{Branch, PathClaim, StringSet};

        let repo = init_repo();
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();
        let coord1 = a("coord1");
        let author = a("zoe");
        let reviewer = a("aiden");

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

        let mut members = epoch.active_members.clone();
        members.insert(
            author.clone(),
            MemberBinding {
                role: Role::Implementor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        members.insert(
            reviewer.clone(),
            MemberBinding {
                role: Role::Reviewer,
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

        for (ag, role) in [(&author, Role::Implementor), (&reviewer, Role::Reviewer)] {
            crate::outbox::submit(
                repo.path(),
                &format!("{ag}-reg"),
                &Candidate::new(
                    ag,
                    &EventData::AgentRegistered(AgentRegistered {
                        display_name: short(ag.as_str()),
                        primary_role: role,
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
                ag,
                &short("host1"),
                0,
                &repo.path().join(format!("_wt_{ag}_reg")),
                &remote,
            )
            .unwrap();
        }

        let coord1_tip = crate::stream::read_stream_tip(repo.path(), &coord1)
            .unwrap()
            .unwrap();
        let author_tip = crate::stream::read_stream_tip(repo.path(), &author)
            .unwrap()
            .unwrap();
        let reviewer_tip = crate::stream::read_stream_tip(repo.path(), &reviewer)
            .unwrap()
            .unwrap();
        crate::publish::publish(
            repo.path(),
            &remote,
            &[
                crate::publish::RefUpdate::new(crate::registry::REGISTRY_REF, new_epoch.id.clone()),
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&coord1).into_string(),
                    coord1_tip,
                ),
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&author).into_string(),
                    author_tip,
                ),
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&reviewer).into_string(),
                    reviewer_tip,
                ),
            ],
        )
        .unwrap();

        let previous_main = crate::gitrepo::rev_parse(repo.path(), "main").unwrap();
        git(
            repo.path(),
            &["checkout", "--quiet", "--detach", &previous_main],
        );
        std::fs::write(repo.path().join("feature.txt"), "feature content\n").unwrap();
        git(repo.path(), &["add", "."]);
        let message = match trailer_agent {
            Some(a) => format!("add feature\n\nAgent-Bus-Agent: {a}"),
            None => "add feature".to_string(),
        };
        git(repo.path(), &["commit", "-q", "-m", &message]);
        let feature_commit = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        git(repo.path(), &["checkout", "--quiet", "main"]);

        let review_scope =
            StringSet::from_iter(vec![PathClaim::parse("feature.txt".into()).unwrap()]);
        let nominate_data = EventData::ReviewNominated(ReviewNominated {
            authors: StringSet::from_iter(vec![author.clone()]),
            product_branch: Branch::parse("refs/heads/agent/zoe/feature".into()).unwrap(),
            reviewer: reviewer.clone(),
            required_checks: vec![text("build")],
            review_scope,
            summary: text("add feature"),
            target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        });
        crate::outbox::submit(
            repo.path(),
            "nominate",
            &Candidate::new(&author, &nominate_data, vec![]),
        )
        .unwrap();
        let nominate_drained = drain_outbox(
            repo.path(),
            repo.path(),
            &author,
            &short("host1"),
            0,
            &repo.path().join("_wt_nominate"),
            &remote,
        )
        .unwrap();
        assert!(
            nominate_drained.rejected.is_empty(),
            "{:?}",
            nominate_drained.rejected
        );
        let nomination = nominate_drained.published[0].clone();

        crate::outbox::submit(
            repo.path(),
            "accept",
            &Candidate::new(
                &reviewer,
                &EventData::ReviewNominationAccepted(ReviewNominationAccepted {
                    nomination: nomination.clone(),
                    note: text("ok"),
                }),
                vec![nomination.clone()],
            ),
        )
        .unwrap();
        let accept_drained = drain_outbox(
            repo.path(),
            repo.path(),
            &reviewer,
            &short("host1"),
            0,
            &repo.path().join("_wt_accept"),
            &remote,
        )
        .unwrap();
        assert!(
            accept_drained.rejected.is_empty(),
            "{:?}",
            accept_drained.rejected
        );

        // Push the author's and reviewer's advanced streams (with the
        // nomination/acceptance) too, so the eventual `review.merge_
        // authorized` candidate's own gate-17 fetch sees a chain that
        // actually resolves.
        let author_tip2 = crate::stream::read_stream_tip(repo.path(), &author)
            .unwrap()
            .unwrap();
        let reviewer_tip2 = crate::stream::read_stream_tip(repo.path(), &reviewer)
            .unwrap()
            .unwrap();
        crate::publish::publish(
            repo.path(),
            &remote,
            &[
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&author).into_string(),
                    author_tip2,
                ),
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&reviewer).into_string(),
                    reviewer_tip2,
                ),
            ],
        )
        .unwrap();

        ReviewFixture {
            repo,
            origin,
            remote,
            coord1,
            author,
            reviewer,
            nomination,
            feature_commit,
            previous_main,
        }
    }

    fn merge_authorized_candidate(f: &ReviewFixture, candidate: &str) -> Candidate {
        use crate::common::{CheckOutcome, CheckResult};
        use crate::events::{EventData, ReviewMergeAuthorized};
        use crate::scalars::{Branch, PathClaim, StringSet};

        let data = ReviewMergeAuthorized {
            nomination: f.nomination.clone(),
            product_branch: Branch::parse("refs/heads/agent/zoe/feature".into()).unwrap(),
            previous_main: ObjectId::parse(f.previous_main.clone()).unwrap(),
            reviewed_commit: ObjectId::parse(f.feature_commit.clone()).unwrap(),
            candidate: ObjectId::parse(candidate.to_string()).unwrap(),
            // No `merge_engine.activated` event exists in this fixture (a
            // real, separate, pre-existing gap in this bus: as of this
            // writing there is no production path that can ever populate
            // `current_merge_engine_epoch` at all -- see this task's final
            // report), so `apply_review_merge_authorized`'s own downstream
            // `merge_engine_epoch` check always fails regardless of this
            // value. That is fine here: every test below either expects
            // rejection *from this gate* before that point is ever reached,
            // or (the one "everything this gate checks is valid" positive
            // test) explicitly asserts the rejection it still sees is that
            // known, unrelated downstream one -- proof this gate itself let
            // the candidate through. Must still be a *structurally real*
            // event (coord1's own actual registration, not a made-up future
            // seq): `dry_run`'s gate-4 recheck (round-5 review) now rejects
            // any reference this event's complete frontier doesn't actually
            // cover, before the downstream check below ever runs.
            merge_engine_epoch: EventId::new(&f.coord1, 0),
            checks: vec![CheckResult {
                command: text("build"),
                result: CheckOutcome::Passed,
                evidence: None,
            }],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter(vec![
                PathClaim::parse("feature.txt".into()).unwrap()
            ]),
            limitations: vec![],
            summary: text("looks good"),
        };
        Candidate::new(&f.reviewer, &EventData::ReviewMergeAuthorized(data), vec![])
    }

    fn drain_reviewer(f: &ReviewFixture) -> DrainResult {
        drain_outbox(
            f.repo.path(),
            f.repo.path(),
            &f.reviewer,
            &short("host1"),
            0,
            &f.repo.path().join("_wt_authorize"),
            &f.remote,
        )
        .unwrap()
    }

    #[test]
    fn drain_outbox_rejects_review_merge_authorized_with_a_commit_missing_the_author_trailer() {
        let f = build_review_fixture(None);
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("has no Agent-Bus-Agent trailer"),
            "{}",
            drained.rejected[0].reason
        );
    }

    #[test]
    fn drain_outbox_rejects_review_merge_authorized_when_the_reviewer_authored_a_commit() {
        let f = build_review_fixture(Some("aiden"));
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("ineligible to merge"),
            "{}",
            drained.rejected[0].reason
        );
    }

    #[test]
    fn drain_outbox_rejects_review_merge_authorized_when_authors_dont_match_the_nomination() {
        // "carol" is neither the reviewer ("aiden") nor the nomination's
        // declared author ("zoe") -- a distinct failure mode from the
        // reviewer-authored case above.
        let f = build_review_fixture(Some("carol"));
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("do not match nomination authors"),
            "{}",
            drained.rejected[0].reason
        );
    }

    #[test]
    fn drain_outbox_rejects_review_merge_authorized_with_a_candidate_that_does_not_reconstruct() {
        let f = build_review_fixture(Some("zoe"));
        // A syntactically valid but *wrong* candidate id -- never actually
        // built by `merge_candidate::reconstruct_candidate`.
        let bogus_candidate = "f".repeat(40);
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &bogus_candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("does not match the deterministic reconstruction"),
            "{}",
            drained.rejected[0].reason
        );
    }

    #[test]
    fn drain_outbox_rejects_review_merge_authorized_with_no_candidate_tag_at_all() {
        let f = build_review_fixture(Some("zoe"));
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        // Deliberately never tagged, locally or otherwise.
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("is not fetchable from"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// The tag exists in the reviewer's own local clone (so `tag_exists_at`
    /// alone would pass) but was deliberately never pushed to `remote` --
    /// `remote_tag_matches`'s own real `ls-remote` is what must catch this,
    /// exactly the g-reviewer:4-class gap v1's identical fix closed.
    #[test]
    fn drain_outbox_rejects_review_merge_authorized_with_a_candidate_tag_that_never_reached_origin()
    {
        let f = build_review_fixture(Some("zoe"));
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        let tag = crate::merge_candidate::candidate_tag_name(&f.reviewer, &candidate);
        crate::gitrepo::tag_lightweight(f.repo.path(), &tag, &candidate).unwrap();
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("is not fetchable from"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// Everything this gate itself checks is genuinely valid: real
    /// authorship, a candidate that matches the deterministic
    /// reconstruction exactly, and a tag both local and pushed to `remote`.
    /// This crate has no production path yet that can populate
    /// `current_merge_engine_epoch` (see `merge_authorized_candidate`'s own
    /// comment) -- a real, separate, pre-existing gap this task does not
    /// fix -- so full end-to-end acceptance is not yet reachable. What this
    /// test instead proves is that this gate specifically did *not* reject
    /// the candidate: the rejection reason that does surface names the
    /// known unrelated downstream cause, not any of this gate's own error
    /// text.
    #[test]
    fn drain_outbox_review_merge_authorized_gate_passes_a_genuinely_valid_candidate() {
        let f = build_review_fixture(Some("zoe"));
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        let tag = crate::merge_candidate::candidate_tag_name(&f.reviewer, &candidate);
        crate::gitrepo::tag_lightweight(f.repo.path(), &tag, &candidate).unwrap();
        let push = crate::gitrepo::run(
            f.repo.path(),
            &["push", &f.remote, &format!("refs/tags/{tag}")],
        )
        .unwrap();
        assert!(push.success, "{push:?}");
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        let reason = &drained.rejected[0].reason;
        assert!(
            reason.contains("is not the currently selected merge engine epoch"),
            "expected the known downstream merge_engine_epoch rejection, got: {reason}"
        );
        for this_gates_own_text in [
            "has no Agent-Bus-Agent trailer",
            "ineligible to merge",
            "do not match nomination authors",
            "does not match the deterministic reconstruction",
            "candidate tag is not fetchable",
            "is not fetchable from",
        ] {
            assert!(
                !reason.contains(this_gates_own_text),
                "rejection should not come from verify_review_merge_authorized, got: {reason}"
            );
        }
    }

    /// The exact scenario `verify_review_merge_authorized`'s doc comment
    /// describes: `prepare-merge` tags and pushes the candidate from one
    /// checkout, but `drain_outbox` for the resulting `review.merge_
    /// authorized` runs from a *different* checkout that has never fetched
    /// that tag -- simulated here by deleting the local tag ref right after
    /// pushing it, which leaves this checkout in exactly the state a fresh
    /// second checkout would be in with respect to this gate's own checks
    /// (`remote_tag_matches` is a pure `ls-remote` against `remote`, with no
    /// dependency on any other local state). Before this fix this hard-
    /// rejected with "candidate tag is not fetchable before authorization"
    /// even though the tag was genuinely valid and pushed -- a real,
    /// severe bug: any host whose checkout didn't happen to be the one that
    /// ran `prepare-merge` could never validly drain the authorization.
    #[test]
    fn drain_outbox_review_merge_authorized_gate_accepts_a_tag_never_fetched_into_this_checkout() {
        let f = build_review_fixture(Some("zoe"));
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        let tag = crate::merge_candidate::candidate_tag_name(&f.reviewer, &candidate);
        crate::gitrepo::tag_lightweight(f.repo.path(), &tag, &candidate).unwrap();
        let push = crate::gitrepo::run(
            f.repo.path(),
            &["push", &f.remote, &format!("refs/tags/{tag}")],
        )
        .unwrap();
        assert!(push.success, "{push:?}");
        // This checkout now forgets the tag it just pushed -- it never
        // "fetched" it, exactly like a checkout that didn't run prepare-merge.
        let untag = crate::gitrepo::run(
            f.repo.path(),
            &["update-ref", "-d", &format!("refs/tags/{tag}")],
        )
        .unwrap();
        assert!(untag.success, "{untag:?}");
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &candidate),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        let reason = &drained.rejected[0].reason;
        assert!(
            reason.contains("is not the currently selected merge engine epoch"),
            "expected the known downstream merge_engine_epoch rejection, got: {reason}"
        );
        for this_gates_own_text in [
            "has no Agent-Bus-Agent trailer",
            "ineligible to merge",
            "do not match nomination authors",
            "does not match the deterministic reconstruction",
            "candidate tag is not fetchable",
            "is not fetchable from",
        ] {
            assert!(
                !reason.contains(this_gates_own_text),
                "rejection should not come from verify_review_merge_authorized, got: {reason}"
            );
        }
    }

    /// A `review.merge_authorized` naming an unknown nomination must not be
    /// rejected by this gate's own text -- `apply::dry_run` reports that
    /// moments later with a clearer, nomination-specific message (see
    /// `verify_review_merge_authorized`'s doc comment).
    #[test]
    fn drain_outbox_defers_unknown_nomination_in_review_merge_authorized_to_dry_run() {
        let f = build_review_fixture(Some("zoe"));
        // Names a real, in-frontier event (the author's own registration)
        // that simply isn't a nomination -- not an out-of-range seq, which
        // `dry_run`'s gate-4 recheck (round-5 review) would now reject
        // before ever reaching the nomination-specific check this test
        // means to exercise.
        let bogus_nomination = EventId::new(&f.author, 0);
        let mut candidate = merge_authorized_candidate(&f, &"a".repeat(40));
        candidate.data["nomination"] = serde_json::json!(bogus_nomination.as_str());
        crate::outbox::submit(f.repo.path(), "auth", &candidate).unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("unknown nomination"),
            "{}",
            drained.rejected[0].reason
        );
    }

    // ---------------------------------------------------------------
    // `review.merge_reconciled`'s git-linked gate (AGENT_REVIEW.md section
    // 11; see `verify_review_merge_reconciled`'s own doc comment). Mirrors
    // the shipped version-one helper's `review_cmds.rs` falsifying test
    // pair (`reconcile_rejects_non_first_parent_successor`/`reconcile_
    // succeeds_when_main_was_advanced_out_of_band`) plus the two "no-op,
    // defer to `apply::dry_run`" branches this gate shares in spirit with
    // `verify_review_merge_authorized`'s own identical pair.

    fn minimal_config() -> crate::bootstrap::BusConfig {
        crate::bootstrap::BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: ObjectId::parse("0".repeat(40)).unwrap(),
            merge_engine: crate::bootstrap::SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
        }
    }

    fn no_frontier() -> crate::frontier::ObservedFrontier {
        crate::frontier::ObservedFrontier::sparse(ObjectId::parse("0".repeat(40)).unwrap(), [])
    }

    /// Inserts a bare `review.merge_authorized` event (no review chain --
    /// `verify_review_merge_reconciled` only ever needs `state.events` to
    /// resolve `d.authorization` to the right *kind* of event, not a real
    /// chain: the nomination-chain-consistency half is `apply_review_merge_
    /// reconciled`'s own job) naming `previous_main`/`reviewed_commit`/
    /// `candidate`, and returns its id.
    fn state_with_bare_authorization(
        previous_main: &str,
        reviewed_commit: &str,
        candidate: &str,
    ) -> (crate::state::BusState, EventId) {
        use crate::events::ReviewMergeAuthorized;
        use crate::scalars::{Branch, PathClaim, StringSet};
        let mut state = crate::state::BusState::new(minimal_config());
        let data = ReviewMergeAuthorized {
            nomination: EventId::new(&a("zoe"), 0),
            product_branch: Branch::parse("refs/heads/agent/zoe/feature".into()).unwrap(),
            previous_main: ObjectId::parse(previous_main.to_string()).unwrap(),
            reviewed_commit: ObjectId::parse(reviewed_commit.to_string()).unwrap(),
            candidate: ObjectId::parse(candidate.to_string()).unwrap(),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter([PathClaim::parse("feature.txt".into()).unwrap()]),
            limitations: vec![],
            summary: text("looks good"),
        };
        let env = Envelope::new(
            &a("aiden"),
            0,
            no_frontier(),
            &EventData::ReviewMergeAuthorized(data),
            [],
        );
        let id = env.id.clone();
        state.events.insert(id.clone(), env);
        (state, id)
    }

    fn reconciled_data(
        authorization: &EventId,
        previous_main: &str,
        reviewed_commit: &str,
        main_commit: &str,
    ) -> crate::events::ReviewMergeReconciled {
        use crate::scalars::Branch;
        crate::events::ReviewMergeReconciled {
            authorization: authorization.clone(),
            previous_main: ObjectId::parse(previous_main.to_string()).unwrap(),
            main_commit: ObjectId::parse(main_commit.to_string()).unwrap(),
            product_branch: Branch::parse("refs/heads/agent/zoe/feature".into()).unwrap(),
            reviewed_commit: ObjectId::parse(reviewed_commit.to_string()).unwrap(),
            reason: text("manual merge outside the bus"),
            user_authority: text("repo owner"),
        }
    }

    #[test]
    fn verify_review_merge_reconciled_rejects_when_main_was_never_advanced() {
        let dir = init_repo();
        let previous_main = crate::gitrepo::rev_parse(dir.path(), "main").unwrap();
        let next = author_commit_for_reconcile(dir.path(), &previous_main, "feature.txt");
        let (state, auth_id) = state_with_bare_authorization(&previous_main, &next, &next);
        let d = reconciled_data(&auth_id, &previous_main, &next, &next);
        let err = verify_review_merge_reconciled(dir.path(), &state, &d).unwrap_err();
        assert!(
            err.to_string().contains("not a first-parent successor"),
            "{err}"
        );
    }

    #[test]
    fn verify_review_merge_reconciled_accepts_when_main_was_genuinely_advanced() {
        let dir = init_repo();
        let previous_main = crate::gitrepo::rev_parse(dir.path(), "main").unwrap();
        let next = author_commit_for_reconcile(dir.path(), &previous_main, "feature.txt");
        git(dir.path(), &["update-ref", "refs/heads/main", &next]);
        let (state, auth_id) = state_with_bare_authorization(&previous_main, &next, &next);
        let d = reconciled_data(&auth_id, &previous_main, &next, &next);
        verify_review_merge_reconciled(dir.path(), &state, &d).expect("must accept");
    }

    /// An unknown `authorization` id must not be rejected by this gate's own
    /// text -- `apply::dry_run` reports that moments later via `apply_
    /// review_merge_reconciled`'s own clearer, authorization-specific
    /// message (see `verify_review_merge_reconciled`'s doc comment).
    #[test]
    fn verify_review_merge_reconciled_is_a_no_op_for_an_unknown_authorization() {
        let dir = init_repo();
        let previous_main = crate::gitrepo::rev_parse(dir.path(), "main").unwrap();
        // `main` deliberately never advanced -- if this gate did not defer,
        // it would reject on the live-Git check instead of the (correct)
        // no-op, and this test would still pass for the wrong reason. The
        // companion "genuinely advanced" test above already proves the
        // live-Git branch itself is reachable and load-bearing.
        let state = crate::state::BusState::new(minimal_config());
        let bogus = EventId::new(&a("aiden"), 99);
        let d = reconciled_data(&bogus, &previous_main, &previous_main, &previous_main);
        verify_review_merge_reconciled(dir.path(), &state, &d)
            .expect("unknown authorization defers to apply::dry_run, not a hard reject here");
    }

    /// `authorization` resolving to a real event that is *not* a `review.
    /// merge_authorized` (e.g. someone's own registration id, reused by
    /// mistake) must likewise defer rather than reject here.
    #[test]
    fn verify_review_merge_reconciled_is_a_no_op_when_authorization_names_the_wrong_kind_of_event()
    {
        let dir = init_repo();
        let previous_main = crate::gitrepo::rev_parse(dir.path(), "main").unwrap();
        let mut state = crate::state::BusState::new(minimal_config());
        let wrong_kind_env = Envelope::new(
            &a("aiden"),
            0,
            no_frontier(),
            &EventData::AgentRegistered(crate::events::AgentRegistered {
                display_name: short("aiden"),
                primary_role: Role::Reviewer,
                purpose: text("x"),
                product_base: None,
                product_branch: None,
                provider: None,
                model: None,
            }),
            [],
        );
        let wrong_kind_id = wrong_kind_env.id.clone();
        state.events.insert(wrong_kind_id.clone(), wrong_kind_env);
        let d = reconciled_data(
            &wrong_kind_id,
            &previous_main,
            &previous_main,
            &previous_main,
        );
        verify_review_merge_reconciled(dir.path(), &state, &d)
            .expect("wrong-kind authorization defers to apply::dry_run, not a hard reject here");
    }

    /// A minimal single-commit-on-`previous_main` helper local to this test
    /// section -- deliberately not reusing `ReviewFixture`'s heavier
    /// `commit_feature_with_trailer`-equivalent setup, since these four
    /// tests exercise `verify_review_merge_reconciled` directly and need
    /// nothing beyond "one more real commit reachable from `base`".
    fn author_commit_for_reconcile(path: &Path, base: &str, file: &str) -> String {
        git(path, &["checkout", "--quiet", "--detach", base]);
        std::fs::write(path.join(file), "content\n").unwrap();
        git(path, &["add", file]);
        git(
            path,
            &["commit", "-q", "-m", "add feature\n\nAgent-Bus-Agent: zoe"],
        );
        let commit = git(path, &["rev-parse", "HEAD"]);
        git(path, &["checkout", "--quiet", "main"]);
        commit
    }

    // ---------------------------------------------------------------
    // The same gate, now proven actually wired into `drain_outbox` for a
    // real, genuinely-published authorization -- not merely called
    // correctly in isolation. Reuses `ReviewFixture` plus a local `merge_
    // engine.activated` activation (this test section's own analogue of
    // `tests/cli_flow.rs`'s `activate_merge_engine` helper, which the
    // existing `review.merge_authorized` gate tests above deliberately
    // don't need since they stop at proving *this* gate's own rejection/
    // acceptance, not a full publish -- see `merge_authorized_candidate`'s
    // own comment on that pre-existing, separate gap).

    fn activate_merge_engine_for(f: &ReviewFixture) -> EventId {
        use crate::events::MergeEngineActivated;
        let data = MergeEngineActivated {
            previous_epoch: EventId::new(&f.coord1, 0),
            merge_engine: short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
            merge_engine_version: short(crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION),
            design_commit: ObjectId::parse("0".repeat(40)).unwrap(),
            helper_commit: ObjectId::parse("0".repeat(40)).unwrap(),
        };
        crate::outbox::submit(
            f.repo.path(),
            "activate",
            &Candidate::new(&f.coord1, &EventData::MergeEngineActivated(data), vec![]),
        )
        .unwrap();
        let drained = drain_outbox(
            f.repo.path(),
            f.repo.path(),
            &f.coord1,
            &short("host1"),
            0,
            &f.repo.path().join("_wt_activate_engine"),
            &f.remote,
        )
        .unwrap();
        assert!(drained.rejected.is_empty(), "{:?}", drained.rejected);
        drained.published[0].clone()
    }

    /// Builds a genuinely valid, genuinely *published* `review.merge_
    /// authorized` on `f` (activating the merge engine first -- otherwise
    /// `apply_review_merge_authorized`'s own downstream check always fails,
    /// see `merge_authorized_candidate`'s comment), and returns `(candidate,
    /// authorization_id)`.
    fn authorized_and_published(f: &ReviewFixture) -> (String, EventId) {
        use crate::common::{CheckOutcome, CheckResult};
        use crate::events::ReviewMergeAuthorized;
        use crate::scalars::{Branch, PathClaim, StringSet};

        let merge_engine_epoch = activate_merge_engine_for(f);
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        let tag = crate::merge_candidate::candidate_tag_name(&f.reviewer, &candidate);
        crate::gitrepo::tag_lightweight(f.repo.path(), &tag, &candidate).unwrap();
        let push = crate::gitrepo::run(
            f.repo.path(),
            &["push", &f.remote, &format!("refs/tags/{tag}")],
        )
        .unwrap();
        assert!(push.success, "{push:?}");

        let data = ReviewMergeAuthorized {
            nomination: f.nomination.clone(),
            product_branch: Branch::parse("refs/heads/agent/zoe/feature".into()).unwrap(),
            previous_main: ObjectId::parse(f.previous_main.clone()).unwrap(),
            reviewed_commit: ObjectId::parse(f.feature_commit.clone()).unwrap(),
            candidate: ObjectId::parse(candidate.clone()).unwrap(),
            merge_engine_epoch,
            checks: vec![CheckResult {
                command: text("build"),
                result: CheckOutcome::Passed,
                evidence: None,
            }],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter([PathClaim::parse("feature.txt".into()).unwrap()]),
            limitations: vec![],
            summary: text("looks good"),
        };
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &Candidate::new(&f.reviewer, &EventData::ReviewMergeAuthorized(data), vec![]),
        )
        .unwrap();
        let drained = drain_reviewer(f);
        assert!(drained.rejected.is_empty(), "{:?}", drained.rejected);
        assert_eq!(drained.published.len(), 1);
        (candidate, drained.published[0].clone())
    }

    fn drain_coord1(f: &ReviewFixture) -> DrainResult {
        drain_outbox(
            f.repo.path(),
            f.repo.path(),
            &f.coord1,
            &short("host1"),
            0,
            &f.repo.path().join("_wt_reconcile"),
            &f.remote,
        )
        .unwrap()
    }

    #[test]
    fn drain_outbox_rejects_review_merge_reconciled_when_main_was_never_advanced() {
        let f = build_review_fixture(Some("zoe"));
        let (candidate, authorization_id) = authorized_and_published(&f);
        // `main` deliberately left at `previous_main` -- the candidate was
        // never actually pushed.
        let d = reconciled_data(
            &authorization_id,
            &f.previous_main,
            &f.feature_commit,
            &candidate,
        );
        crate::outbox::submit(
            f.repo.path(),
            "reconcile",
            &Candidate::new(
                &f.coord1,
                &EventData::ReviewMergeReconciled(d),
                vec![authorization_id],
            ),
        )
        .unwrap();

        let drained = drain_coord1(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("not a first-parent successor"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// The section 11 recovery path succeeding end to end: a real
    /// authorization, `main` genuinely (if manually) advanced to the exact
    /// authorized candidate, and a bootstrap coordinator's `review.merge_
    /// reconciled` actually publishing -- proving `verify_review_merge_
    /// reconciled` is reached from real `drain_outbox`, not merely callable
    /// in isolation (the four `verify_review_merge_reconciled_*` tests
    /// above), and that it does not itself block a genuinely valid
    /// reconciliation.
    #[test]
    fn drain_outbox_accepts_review_merge_reconciled_when_main_was_genuinely_advanced() {
        let f = build_review_fixture(Some("zoe"));
        let (candidate, authorization_id) = authorized_and_published(&f);
        git(
            f.repo.path(),
            &["update-ref", "refs/heads/main", &candidate],
        );

        let d = reconciled_data(
            &authorization_id,
            &f.previous_main,
            &f.feature_commit,
            &candidate,
        );
        crate::outbox::submit(
            f.repo.path(),
            "reconcile",
            &Candidate::new(
                &f.coord1,
                &EventData::ReviewMergeReconciled(d),
                vec![authorization_id],
            ),
        )
        .unwrap();

        let drained = drain_coord1(&f);
        assert!(drained.rejected.is_empty(), "{:?}", drained.rejected);
        assert_eq!(drained.published.len(), 1);
    }
}
