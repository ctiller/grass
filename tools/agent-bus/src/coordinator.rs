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
    remote: &str,
) -> AbResult<DrainResult> {
    // Custody is authorized *before* the empty-outbox shortcut, not after.
    //
    // Gate 6 requires duplicate custody of one agent stream to fail closed,
    // and `registry.rs` claims `authorize_stream_write` is "called by every
    // future `drain_outbox`/`publish_stream`". It was not: the early return
    // below sat in front of it, so whenever the outbox happened to be empty
    // this function returned success without checking custody at all, and
    // `drain_and_publish` went on to push the agent's stream ref. That is
    // reachable without contrivance -- a coordinator whose earlier drain
    // committed locally but failed to push has an empty outbox and a local
    // tip ahead of origin, so after custody moves away it could still
    // fast-forward the new custodian's ref. No force-push required, which is
    // exactly the shape gate 6 says must be impossible.
    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists yet"))?;
    let epoch = crate::registry::read_epoch(repo, &registry_tip)?;
    crate::registry::authorize_stream_write(&epoch, agent, host, coordinator_custody_epoch)?;

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
        match crate::sync::synced_snapshot(repo, git_common_dir, remote) {
            Ok(snap) => fresh_state = Some(snap.state),
            Err(e) => fresh_sync_err = Some(e.to_string()),
        }
    }

    // The fetch above writes `refs/heads/agent-registry`, so the epoch read
    // before it may now be superseded. Re-read it, and re-authorize custody
    // against the fresh one.
    //
    // The comment above used to claim the fetch came first precisely so this
    // could not happen; it did not, and the consequence is specific to a
    // complete frontier. `build_frontier` below would have built one for the
    // *older* epoch, and `apply::require_complete_frontier` validates against
    // whatever epoch the frontier names -- which reduction deliberately keeps
    // in `known_epochs` -- so the report would have been accepted while
    // omitting exactly the members the fetch had just revealed. That is
    // assurance without evidence, which is what requiring a complete frontier
    // was meant to prevent. It also meant gate 6/7's custody check ran
    // against a pre-fetch view.
    let (registry_tip, epoch) = if fresh_state.is_some() {
        let tip = crate::registry::read_registry_tip(repo)?
            .ok_or_else(|| invalid("no registry root exists yet"))?;
        let fresh_epoch = crate::registry::read_epoch(repo, &tip)?;
        crate::registry::authorize_stream_write(
            &fresh_epoch,
            agent,
            host,
            coordinator_custody_epoch,
        )?;
        (tip, fresh_epoch)
    } else {
        (registry_tip, epoch)
    };
    let _ = registry_tip;

    let mut state = match fresh_state {
        Some(s) => s,
        None => crate::sync::cached_snapshot(repo, git_common_dir)?.state,
    };

    let existing_tip = crate::stream::read_stream_tip(repo, agent)?;
    let mut next_seq = if let Some(tip) = &existing_tip {
        let reader = crate::gitobjects::Libgit2Reader::open(repo)?;
        crate::storage::read_stream_log_at(&reader, tip, agent)?.len() as u64
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
            if let Err(e) = verify_review_merge_reconciled(repo, remote, &state, d) {
                let reason = e.to_string();
                reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
                rejected.push(RejectedCandidate {
                    kind: candidate.kind.clone(),
                    reason,
                });
                continue;
            }
        }
        // Gate 12's "audience resolution is exact". `apply` deliberately
        // does not check it -- see `apply_broadcast_published` -- because
        // the state it resolves against is mutable, unpinned, and routinely
        // not yet applied when the broadcast is replayed. Here it is: this
        // is the publishing host, `state` is its freshly-fetched reduction,
        // and the publisher is claiming a snapshot it computed from exactly
        // this view moments ago.
        if let crate::events::EventData::BroadcastPublished(d) = &data {
            if let Err(e) = verify_broadcast_published(&state, d) {
                let reason = e.to_string();
                reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
                rejected.push(RejectedCandidate {
                    kind: candidate.kind.clone(),
                    reason,
                });
                continue;
            }
        }
        if let Err(e) = verify_schema_activation_advances(&state, &data) {
            let reason = e.to_string();
            reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
            rejected.push(RejectedCandidate {
                kind: candidate.kind.clone(),
                reason,
            });
            continue;
        }
        if let Err(e) = verify_author_active(&state, agent, &data) {
            let reason = e.to_string();
            reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
            rejected.push(RejectedCandidate {
                kind: candidate.kind.clone(),
                reason,
            });
            continue;
        }
        if let Err(e) = verify_participants_active(&state, &data) {
            let reason = e.to_string();
            reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
            rejected.push(RejectedCandidate {
                kind: candidate.kind.clone(),
                reason,
            });
            continue;
        }
        if let Err(e) = verify_predecessor_not_contested(&state, &data) {
            let reason = e.to_string();
            reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
            rejected.push(RejectedCandidate {
                kind: candidate.kind.clone(),
                reason,
            });
            continue;
        }
        // AGENT_BUS_SCHEMA.md section 8's "inherited_findings equals every
        // still-open finding". `apply` checks only that no finding is named
        // twice, which is all it can soundly do -- the chain's open set is
        // moved by other agents' events that a reassignment neither
        // references nor need have observed, so holding a published event to
        // it during replay took the fleet down. Here `state` is this host's
        // fully-reduced view and the publisher is claiming a set it computed
        // from exactly this view moments ago.
        if let Err(e) = verify_review_reassignment_inherits_open_findings(&state, &data) {
            let reason = e.to_string();
            reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
            rejected.push(RejectedCandidate {
                kind: candidate.kind.clone(),
                reason,
            });
            continue;
        }
        if let Err(e) = verify_object_ids_resolve(repo, &data) {
            let reason = e.to_string();
            reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
            rejected.push(RejectedCandidate {
                kind: candidate.kind.clone(),
                reason,
            });
            continue;
        }
        // A frontier this host cannot build rejects *this* candidate, with a
        // durable receipt, exactly like every other check in this loop.
        //
        // It used to be a `?`, which aborted the whole drain: nothing
        // committed, nothing removed from the outbox, no receipt written --
        // and since the condition is a property of the *roster*, not of the
        // candidate, every later `coordinate` for this agent failed
        // identically forever. No CLI command removes a pending candidate, so
        // recovery meant hand-deleting the file. `audit.reported` is what
        // makes that reachable in ordinary use: it is the only kind an
        // ordinary agent publishes that needs a complete frontier, and
        // `build_complete_frontier` fails whenever any active member has not
        // yet published its stream root -- a state `sync.rs` explicitly calls
        // "a real, expected state, not an error".
        let observed = match build_frontier(repo, &epoch, agent, &candidate.extra_refs, &data) {
            Ok(observed) => observed,
            Err(e) => {
                let reason = e.to_string();
                reject_candidate(git_common_dir, agent, path, candidate, &reason)?;
                rejected.push(RejectedCandidate {
                    kind: candidate.kind.clone(),
                    reason,
                });
                continue;
            }
        };
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
        let commit = crate::stream::create_root_commit(repo, &header, &first)?;
        published.push(first.id);
        new_tip = Some(commit);
    }

    if !remaining.is_empty() {
        let commit = crate::stream::append_to_stream(
            repo,
            agent,
            new_tip.as_ref().expect("set above"),
            &remaining,
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
    remote: &str,
) -> AbResult<(DrainResult, crate::publish::PublicationReceipt)> {
    let drained = drain_outbox(
        repo,
        git_common_dir,
        agent,
        host,
        coordinator_custody_epoch,
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
    author: &Agent,
    extra_refs: &[EventId],
    data: &crate::events::EventData,
) -> AbResult<ObservedFrontier> {
    if requires_complete_frontier(data) {
        return build_complete_frontier(repo, epoch);
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
    let reader = crate::gitobjects::Libgit2Reader::open(repo)?;
    for (ref_agent, r) in through {
        let tip = crate::stream::read_stream_tip(repo, &ref_agent)?.ok_or_else(|| {
            invalid(format!(
                "cannot build a frontier entry for {ref_agent}: it has no stream"
            ))
        })?;
        // The referenced event must actually exist in that stream.
        //
        // This used to be a TODO, and the gap was not theoretical: it is how
        // `e-auditor:10` came to cite `c-reviewer:100`, one past that
        // stream's tip. `through` is taken from whatever the caller
        // referenced, so nothing here checked the id named anything, and the
        // event published. Every host then failed to reduce the bus, and
        // because the log is append-only nothing could withdraw it -- the
        // reducer had to be changed to tolerate the reference at all.
        //
        // Submission is the one place this can be refused. The candidate is
        // still in the author's outbox, so a rejection here costs a durable
        // receipt and a retry; past publication, it costs the fleet.
        let log_len = crate::storage::read_stream_log_at(&reader, &tip, &ref_agent)?.len() as u64;
        if r.seq() >= log_len {
            return Err(invalid(format!(
                "{r} does not exist: {ref_agent}'s stream ends at {}",
                EventId::new(&ref_agent, log_len.saturating_sub(1))
            )));
        }
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
/// authorship` against the *submitted* payload (`d`) -- not merely trusting
/// that `cli::prepare_merge` was ever run, or run honestly -- confirms the
/// candidate tag `prepare-merge` would have published is independently
/// fetchable from `remote` (`gitrepo::remote_tag_matches`, a real
/// `ls-remote`), and validates the object that tag names against the
/// payload (`merge_candidate::verify_candidate_object`/`verify_candidate_
/// scope`) rather than rebuilding the merge locally. Deliberately does
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
    // AGENT_BUS_SCHEMA.md section 10: an unresolved issue whose `blocks` set
    // names an event in the active nomination chain blocks authorization.
    //
    // This is the publication-time verdict, and publication time is the only
    // place it can honestly be reached. `apply` cannot ask it: reduction
    // orders events by `refs`, never by `observed`, so during replay an
    // authorization is routinely applied before an issue its own frontier
    // saw, and any answer there depends on the lexicographic accident of two
    // agent names -- while a host that had fetched the issue would be unable
    // to reduce the bus at all. Here there is no replay order to be at the
    // mercy of: `state` is this host's fully-reduced view, freshly fetched by
    // `drain_outbox`, and the question "can I already see that this chain is
    // blocked?" has one answer.
    //
    // Cheap, and deliberately ahead of the candidate reconstruction below,
    // which shells out to Git repeatedly.
    if let Some(blocking) = crate::apply::blocking_issue_for_chain(state, chain) {
        return Err(invalid(format!(
            "issue {blocking} is unresolved and blocks nomination chain {}; resolve or reject it before authorizing the merge",
            d.nomination
        )));
    }
    // Deliberately no local-only `tag_exists_at` precondition here: `drain_outbox`
    // may run from any checkout, not just the one `prepare-merge` ran from, and a
    // tag `prepare-merge` pushed from a *different* checkout is genuinely valid
    // even though this checkout has never fetched it. `remote_tag_matches` (a real
    // `ls-remote`) is the checkout-independent, authoritative check for "other
    // agents could verify this merge" -- see its own doc comment -- so it alone is
    // both necessary and sufficient for *publication* of the tag.
    let tag = crate::merge_candidate::candidate_tag_name(reviewer, d.candidate.as_str());
    if !crate::gitrepo::remote_tag_matches(repo, remote, &tag, d.candidate.as_str())? {
        return Err(invalid(format!(
            "candidate tag refs/tags/{tag} is not fetchable from {remote}; other agents could \
             not verify this merge"
        )));
    }
    // This gate used to rebuild the merge here with this host's own `git
    // merge-tree --write-tree` and require the result to equal `d.candidate`,
    // which is what made an installed git version protocol authority: a
    // coordinator on a different build rejected a perfectly honest
    // reviewer's authorization, and the only remedy on offer was to make
    // every host in the fleet compile one particular git. The repository
    // owner rejected that design (g-design:249).
    //
    // So validate the object the tag actually names instead. The tag is
    // immutable and was just confirmed on `remote`, so fetching it here is
    // reading the same bytes every other agent will read -- not a local
    // re-derivation of what they *should* have been.
    crate::merge_candidate::fetch_candidate_tag(repo, remote, reviewer, d.candidate.as_str())?;
    // Deliberately after that fetch. This gate may run from any checkout,
    // including one that has only ever seen `main` and the bus -- the
    // reviewed commits themselves reach it through the candidate's own
    // history, since the candidate has `reviewed_commit` as a parent. Asking
    // about authorship first made a coordinator on a second clone fail with
    // "does not name an object" for a perfectly valid authorization; the
    // reconstruction that used to sit here hid it, because the only hosts
    // that got this far had already built the merge locally.
    let expected_authors: std::collections::BTreeSet<Agent> =
        chain.current_request.authors.iter().cloned().collect();
    crate::merge_candidate::verify_authorship(
        repo,
        reviewer,
        &expected_authors,
        d.previous_main.as_str(),
        d.reviewed_commit.as_str(),
    )?;
    crate::merge_candidate::verify_candidate_object(
        repo,
        reviewer,
        d.previous_main.as_str(),
        d.reviewed_commit.as_str(),
        d.candidate.as_str(),
    )?;
    // The content bound: a candidate nobody rebuilds is still not allowed to
    // touch anything outside the scope this nomination was reviewed against.
    // Checked here as well as in `merge_ready` because this is the
    // publication boundary -- a hand-crafted `submit --kind
    // review.merge_authorized` never runs `merge-ready` at all.
    crate::merge_candidate::verify_candidate_scope(
        repo,
        d.previous_main.as_str(),
        d.candidate.as_str(),
        d.reviewed_scope.as_slice(),
    )?;
    // The `checks` half of the binding is already enforced, and enforced
    // somewhere that cannot drift: `apply_review_merge_authorized` requires
    // every one of the nomination's `required_checks` to appear in
    // `d.checks`, at reduction time, on every host. That check never touched
    // the merge engine, so nothing here needs to move or be duplicated.
    // Checked last, after this gate's own candidate work, so a candidate
    // that is wrong in a more specific way still says so.
    // `apply` checks only that the epoch names a real activation, which is
    // all it can soundly do -- a later `merge_engine.activated` moves
    // `current_merge_engine_epoch` and this authorization neither references
    // nor need have observed it, so asking there made reduction itself
    // order-dependent. Here the state is this host's fully-reduced view.
    if Some(&d.merge_engine_epoch) != state.current_merge_engine_epoch.as_ref() {
        return Err(invalid(format!(
            "merge_engine_epoch {} is not the currently selected merge engine epoch ({}); re-run the merge on the current engine before authorizing",
            d.merge_engine_epoch,
            state
                .current_merge_engine_epoch
                .as_ref()
                .map(|e| e.to_string())
                .unwrap_or_else(|| "none selected yet".to_string())
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
///
/// Deliberately fetches `refs/heads/main` from `remote` into a scratch ref
/// rather than trusting this checkout's own local `refs/heads/main`: unlike
/// the bus's own refs, `main` is a product ref entirely outside `sync::
/// synced_snapshot`'s fetch (which only ever pulls the registry/agent-event
/// refs), and `reconcile`'s whole purpose (AGENT_REVIEW.md section 11) is
/// recovery *by a coordinator other than the one who pushed the merge* --
/// exactly the case where this checkout's local `main` may never have been
/// fetched at all (round-6 review: this had the identical checkout
/// -dependence bug round 5 fixed for `verify_review_merge_authorized`'s
/// candidate-tag check, see its own doc comment).
fn verify_review_merge_reconciled(
    repo: &Path,
    remote: &str,
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
    // A receipt already exists for this chain and this host can see it.
    //
    // `apply` refuses only the author's *own* duplicate, which is all it can
    // soundly do: a reviewer's `review.merged` and a coordinator's
    // `review.merge_reconciled` come from different agents who need not have
    // observed each other, so refusing that pairing during replay would make
    // reduction depend on arrival order. Recording both is correct there --
    // `audit_main` asks whether *any* receipt names the commit.
    //
    // But publishing a second one when this host can already see the first
    // is a caller doing something incoherent, and here there is no ordering
    // question: `state` is this host's fully-reduced view. Reconciliation
    // exists for a reviewer that went quiet, so a chain that already carries
    // a receipt is precisely the case that does not need reconciling.
    if let Ok(crate::events::EventData::ReviewMergeAuthorized(auth)) = auth_env.typed_data() {
        if let Some(chain) = state
            .review_chain_by_nomination
            .get(&auth.nomination)
            .and_then(|root| state.reviews.get(root))
        {
            if let Some(existing) = chain.merged.iter().chain(chain.reconciled.iter()).next() {
                return Err(invalid(format!(
                    "this chain already carries receipt {existing}; reconciliation records a merge nobody receipted, not a second receipt for one already recorded"
                )));
            }
        }
    }
    const MAIN_PROBE_REF: &str = "refs/agent-bus/reconcile-main-probe";
    let fetch = crate::gitrepo::fetch_refspecs(
        repo,
        remote,
        &[format!("refs/heads/main:{MAIN_PROBE_REF}")],
    )?;
    if !fetch.success {
        return Err(invalid(format!(
            "could not fetch refs/heads/main from {remote} to verify this reconciliation: {}",
            fetch.stderr
        )));
    }
    let is_first_parent_of_main =
        crate::gitrepo::rev_list_first_parent(repo, d.previous_main.as_str(), MAIN_PROBE_REF)?
            .iter()
            .any(|c| c == d.main_commit.as_str());
    if !is_first_parent_of_main {
        return Err(invalid(format!(
            "main_commit {} is not a first-parent successor of previous_main {} on {remote}'s \
             current main -- reconcile only records a merge that has genuinely already landed",
            d.main_commit, d.previous_main
        )));
    }
    Ok(())
}

/// The *author* of an event whose authority depends on being a live
/// coordinator must still be active.
///
/// The sibling `verify_participants_active` below relocated exactly this
/// question for the agents an event *names*; this is the same relocation
/// for the agent that *writes* it, and it exists because
/// `apply::require_bootstrap_coordinator` can no longer ask. `active()`
/// reads `retired`, which only ever gets set by *another* coordinator's
/// `agent.retired` on a *different* stream -- causally unordered against
/// this event, so during replay the answer depended on fetch order and a
/// retired coordinator's own back-history became fatal on some hosts and
/// harmless on others. Here `state` is the publishing host's fully-reduced
/// view, so there is one answer, and refusing costs nothing recoverable:
/// the author resubmits after `agent.resumed`.
///
/// The listed kinds are every kind whose `apply` handler reaches
/// `require_bootstrap_coordinator`. For the three reassignment kinds that
/// reach it only when the author is *not* the item's opener/author, the
/// check is deliberately unconditional rather than a duplicate of `apply`'s
/// opener/author test: in the other branch the author is the opener or a
/// named review author, and a retired one has no business reassigning its
/// own work either. Kinds an inactive agent legitimately publishes --
/// `agent.resumed` above all, which only a retired agent ever has cause to
/// write -- are deliberately absent.
fn verify_author_active(
    state: &crate::state::BusState,
    agent: &Agent,
    data: &crate::events::EventData,
) -> AbResult<()> {
    use crate::events::EventData as E;
    let needs_live_author = matches!(
        data,
        E::AgentRetired(_)
            | E::SchemaActivated(_)
            | E::MergeEngineActivated(_)
            | E::ReviewMergeReconciled(_)
            | E::LifecycleConflictResolved(_)
            | E::IssueReassigned(_)
            | E::DependencyReassigned(_)
            | E::ReviewReassigned(_)
            // The four whose handlers ask `require_self_active_role`. That
            // checks the publisher has not stood down, which is sound during
            // replay because `agent.status` shares the publisher's stream;
            // it deliberately does not read `retired`, which a coordinator
            // sets from a different stream. This is where the `retired` half
            // is asked instead.
            | E::ScopeSet(_)
            | E::AuditReported(_)
            | E::HandoffOffered(_)
            | E::ReviewNominated(_)
    );
    if !needs_live_author {
        return Ok(());
    }
    match state.agents.get(agent) {
        // Unregistered is `apply`'s own refusal to make, with its own
        // message; not duplicated here.
        None => Ok(()),
        Some(ag) if ag.active() => Ok(()),
        Some(_) => Err(invalid(format!(
            "{agent} is retired or otherwise inactive, so it cannot publish this event"
        ))),
    }
}

/// Every agent this event names must still be active.
///
/// `apply` checks only that they hold the right role, which is fixed at
/// registration and therefore ordered ahead of everything. Liveness is not:
/// `agent.status` and `agent.retired` live on the named agent's own stream,
/// which this event neither references nor need have observed, so asking
/// during replay made a nomination fatal on a host that had fetched the
/// reviewer's retirement and harmless on one that had not.
///
/// Here `state` is the publishing host's fully-reduced view, so a nominator
/// is held to what it could actually have seen.
fn verify_participants_active(
    state: &crate::state::BusState,
    data: &crate::events::EventData,
) -> AbResult<()> {
    use crate::events::EventData as E;
    let named: Vec<&Agent> = match data {
        E::ReviewNominated(d) => d
            .authors
            .iter()
            .chain(std::iter::once(&d.reviewer))
            .collect(),
        E::ReviewReassigned(d) => vec![&d.reviewer],
        _ => return Ok(()),
    };
    for agent in named {
        match state.agents.get(agent) {
            Some(ag) if ag.active() => {}
            Some(_) => {
                return Err(invalid(format!(
                "{agent} is retired or otherwise inactive, so it cannot take part in this review"
            )))
            }
            None => return Err(invalid(format!("{agent} is not a registered agent"))),
        }
    }
    Ok(())
}

/// AGENT_BUS_SCHEMA.md's "a transition may not build on a predecessor whose
/// own disposition is still an open race".
///
/// `apply` cannot ask this. `ExclusiveTracker::is_contested` reads group
/// membership, which grows as concurrent candidates reduce, and nothing this
/// event carries references the candidate that contests its predecessor --
/// so asking during replay made the same two events fatal on one host and
/// harmless on another, decided by which was fetched first.
///
/// Here `state` is the publishing host's own fully-reduced view, so the
/// question has one answer. A publisher that genuinely cannot see the
/// competing claim yet is not stopped, and should not be: it has committed
/// no error, and the resulting group is reconciled by
/// `lifecycle.conflict_resolved` exactly as an ordinary race is.
fn verify_predecessor_not_contested(
    state: &crate::state::BusState,
    data: &crate::events::EventData,
) -> AbResult<()> {
    use crate::events::EventData as E;
    let predecessor = match data {
        E::MergeEngineActivated(d) => &d.previous_epoch,
        E::IssueResolved(d) => &d.assignment,
        E::IssueRejected(d) => &d.assignment,
        E::IssueReassigned(d) => &d.previous_assignment,
        E::DependencyResolved(d) => &d.assignment,
        E::DependencyRejected(d) => &d.assignment,
        E::DependencyReassigned(d) => &d.previous_assignment,
        E::HandoffAccepted(d) => &d.handoff,
        E::HandoffDeclined(d) => &d.handoff,
        E::HandoffWithdrawn(d) => &d.handoff,
        _ => return Ok(()),
    };
    if state.exclusive.is_contested(predecessor) {
        return Err(invalid(format!(
            "{predecessor} is itself part of an unresolved lifecycle conflict; a coordinator must publish lifecycle.conflict_resolved for it before anything builds on it"
        )));
    }
    Ok(())
}

/// Rejects a well-formed-but-nonexistent object id in any of the three
/// fields that carry one as a plain, unvalidated `ObjectId`:
/// `agent.registered`'s `product_base`, `scope.set`'s `base_code_commit`,
/// and `issue.opened`'s `code_commit`. `ObjectId::parse` only checks the
/// 40/64-hex-char *format* -- ported from the shipped version-one helper's
/// identical `register`/`scope_set`/`issue_open` checks (`gitrepo::
/// rev_parse_opt`), a parity gap discovered while preparing this crate's
/// own nomination: v1 gained both checks (`g-design:42`, `c-agent:15`)
/// after this branch had already forked, and nothing in `apply.rs` can
/// catch it -- it deliberately never touches git (see its own module doc).
/// `product_base` is the highest-stakes of the three: `agent.registered` is
/// sequence zero, immutable, never amendable, so a `product_base` that only
/// *looks* like a valid object id would be permanently unrecoverable.
/// `base_code_commit`/`code_commit` are lower-stakes (correctable by a
/// follow-up `scope.set`, or merely evidence rather than a binding field
/// respectively) but the same silent-typo failure mode applies to both.
/// AGENT_BUS_SCHEMA.md section 4: a `schema.activated`'s "`version` is
/// greater than all previously activated versions."
///
/// `apply` cannot ask this. `schema.activated` references no predecessor at
/// all (`SchemaActivated::referenced_ids` is empty), so two activations from
/// different coordinators get no edge between them and `apply::
/// topological_order` is free to replay a higher version first -- which made
/// the lower one fatal on hosts that happened to fetch in that order, and
/// made two coordinators activating the *same* version fatal in both. See
/// `apply::apply_schema_activated`, which now takes the maximum, for the
/// full argument.
///
/// Here `state` is the publishing host's own fully-reduced view, so the
/// question has one answer. A coordinator that genuinely cannot see a
/// concurrent activation yet is not stopped, and should not be: it has
/// committed no error, and the two activations reconcile to the higher
/// version on every host either way.
fn verify_schema_activation_advances(
    state: &crate::state::BusState,
    data: &crate::events::EventData,
) -> AbResult<()> {
    let crate::events::EventData::SchemaActivated(d) = data else {
        return Ok(());
    };
    if d.version <= state.activated_schema_version {
        return Err(invalid(format!(
            "schema version {} is not greater than the currently activated {}",
            d.version, state.activated_schema_version
        )));
    }
    Ok(())
}

/// AGENT_BUS_SCHEMA.md section 8: a `review.reassigned` must inherit every
/// finding still open on the chain, exactly once.
///
/// Asked here rather than in `apply` because the chain's open set is not
/// something a published event can be held to forever. It moves whenever
/// another agent files or disposes of a finding, on a stream the
/// reassignment neither references nor need have observed, so an event that
/// was correct when it published becomes "wrong" later. Reduction has no
/// per-event isolation, so answering that with an `Err` stops every agent
/// reading the bus -- which is exactly what happened.
///
/// `Ok(())` when the chain does not resolve: that is an ordinary validation
/// failure `apply::dry_run` reports moments later with a clearer message.
fn verify_review_reassignment_inherits_open_findings(
    state: &crate::state::BusState,
    data: &crate::events::EventData,
) -> AbResult<()> {
    let crate::events::EventData::ReviewReassigned(d) = data else {
        return Ok(());
    };
    let Some(chain) = state.review_chain(&d.replaces) else {
        return Ok(());
    };
    let still_open: std::collections::BTreeSet<(EventId, String)> = chain
        .findings
        .iter()
        .filter(|(_, f)| f.disposition == crate::state::FindingDisposition::Open)
        .map(|(k, _)| k.clone())
        .collect();
    let inherited: std::collections::BTreeSet<(EventId, String)> = d
        .inherited_findings
        .iter()
        .map(|f| (f.changes_event.clone(), f.finding_id.as_str().to_string()))
        .collect();
    if inherited != still_open {
        let missing: Vec<String> = still_open
            .difference(&inherited)
            .map(|(e, f)| format!("{e}/{f}"))
            .collect();
        let extra: Vec<String> = inherited
            .difference(&still_open)
            .map(|(e, f)| format!("{e}/{f}"))
            .collect();
        return Err(invalid(format!(
            "inherited_findings must equal every still-open finding on this chain: missing {missing:?}, unexpected {extra:?}"
        )));
    }
    Ok(())
}

fn verify_object_ids_resolve(repo: &Path, data: &crate::events::EventData) -> AbResult<()> {
    let candidates: Vec<(&str, &crate::scalars::ObjectId)> = match data {
        crate::events::EventData::AgentRegistered(d) => {
            d.product_base.iter().map(|b| ("product_base", b)).collect()
        }
        crate::events::EventData::ScopeSet(d) => {
            vec![("base_code_commit", &d.base_code_commit)]
        }
        crate::events::EventData::IssueOpened(d) => {
            d.code_commit.iter().map(|c| ("code_commit", c)).collect()
        }
        // An audit report pins the revisions it inspected, which is the same
        // class of evidence as the fields above and fails the same silent way
        // if mistyped: the report reads as authoritative about a commit that
        // does not exist. `apply` already refuses a report naming an issue
        // that does not exist; this is the object-id half of the same rule.
        crate::events::EventData::AuditReported(d) => d
            .inspected_commits
            .iter()
            .map(|c| ("inspected_commits", c))
            .collect(),
        _ => vec![],
    };
    for (field, id) in candidates {
        if crate::gitrepo::rev_parse_opt(repo, id.as_str())?.is_none() {
            return Err(invalid(format!(
                "{field} {id} does not resolve to an object in this repository"
            )));
        }
    }
    Ok(())
}

/// docs/AGENT_COORDINATION_EVOLUTION.md section 4.2, gate 12: the claimed
/// `audience_snapshot` must equal `audience_selector` resolved against
/// `audience_epoch`.
///
/// `Ok(())` when the epoch is not known to this host: that is an ordinary
/// validation failure `apply::dry_run` reports moments later with a
/// clearer, epoch-specific message, so it is not duplicated here.
fn verify_broadcast_published(
    state: &crate::state::BusState,
    d: &crate::events::BroadcastPublished,
) -> AbResult<()> {
    let epoch = match state.known_epochs.get(&d.audience_epoch) {
        Some(e) => e,
        None => return Ok(()),
    };
    let resolved = crate::apply::resolve_audience(state, &d.audience_selector, epoch);
    let claimed: std::collections::BTreeSet<Agent> = d.audience_snapshot.iter().cloned().collect();
    if resolved != claimed {
        let missing: Vec<String> = resolved
            .difference(&claimed)
            .map(|a| a.to_string())
            .collect();
        let extra: Vec<String> = claimed
            .difference(&resolved)
            .map(|a| a.to_string())
            .collect();
        return Err(invalid(format!(
            "audience_snapshot does not match audience_selector resolved against epoch {}: missing {:?}, unexpected {:?}",
            d.audience_epoch, missing, extra
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
        // Section 2.2: the report "pins the inspected product revisions and
        // observed event frontier". A sparse frontier pins one entry per
        // referenced agent, so a clean report -- no issues, no `--observes`
        // -- would publish having pinned *nothing* about the streams it
        // claims to have examined. That is assurance without evidence, which
        // is the specific failure `limitations` exists to prevent, so the one
        // field that records what was observed has to be real.
        //
        // This makes an audit currency-sensitive too (`requires_synced_
        // snapshot` builds on this), so a report cannot be published from a
        // stale local cut. That is the right trade for an assurance artifact:
        // an audit of a view that was already old is worth little, and the
        // event carries no authority whose cost would argue the other way.
        crate::events::EventData::AuditReported(_) => true,
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
    // A broadcast whose audience resolves against `subscribed_topics` or
    // `scope` is currency-sensitive whatever its acknowledgement setting.
    // `verify_broadcast_published` is the *only* place gate 12's exactness
    // is now checked -- reduction has no sound way to ask it -- and
    // resolving a mutable selector against a stale cached cut lets that
    // single check accept a snapshot omitting a subscriber who has already
    // published remotely. Reduction then records the wrong audience, and no
    // later synchronization repairs it. An informational broadcast needs no
    // complete frontier, so `requires_complete_frontier` does not cover it.
    if let EventData::BroadcastPublished(d) = data {
        if crate::apply::broadcast_audience_reads_mutable_state(d) {
            return true;
        }
    }
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
///
/// One reader serves the whole roster. This loop used to check out a fresh
/// worktree per active member on every call; that machinery is gone, and a
/// single open of the object database now serves every member.
fn build_complete_frontier(
    repo: &Path,
    epoch: &crate::registry::RosterEpoch,
) -> AbResult<ObservedFrontier> {
    let reader = crate::gitobjects::Libgit2Reader::open(repo)?;
    let mut entries = Vec::new();
    for member in epoch.active_members.keys() {
        let tip = crate::stream::read_stream_tip(repo, member)?.ok_or_else(|| {
            invalid(format!(
                "cannot build a complete frontier: {member} has not yet published its own stream"
            ))
        })?;
        let log_len = crate::storage::read_stream_log_at(&reader, &tip, member)?.len() as u64;
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

    /// Every fixture here records an engine version no host runs and no
    /// build of this crate ever pinned, so the whole module stands as an
    /// assertion that publication never consults it. Spelling a crate
    /// constant instead would make the fixtures agree with the code under
    /// test by construction, which is how the version pin stayed invisible
    /// to this suite while wedging hosts in the field.
    const FOREIGN_ENGINE_VERSION: &str = "1.2.3-no-build-ever-pinned-this";

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

    /// Gate 6: "duplicate custody of one agent stream fails closed without
    /// force-push."
    ///
    /// The authorization used to sit *after* the empty-outbox shortcut, so a
    /// custodian the registry had superseded was never checked whenever it
    /// happened to have nothing pending -- and `drain_and_publish` would then
    /// push that agent's stream ref anyway. The dangerous case needs no
    /// contrivance: a coordinator whose earlier drain committed locally but
    /// failed to push has an empty outbox and a local tip ahead of origin, so
    /// once custody moves it can still fast-forward the new custodian's ref.
    ///
    /// Asserted with an empty outbox specifically, because with a non-empty
    /// one the check was always reached and the bug was invisible.
    #[test]
    fn drain_outbox_refuses_a_wrong_custodian_even_with_nothing_pending() {
        let repo = init_repo();
        let coord1 = a("coord1");
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap()).unwrap(),
            short("host1"),
        )
        .unwrap();

        assert!(
            crate::outbox::list_pending(repo.path(), &coord1)
                .unwrap()
                .is_empty(),
            "fixture must have an empty outbox, or it tests the wrong path"
        );

        // The rightful custodian is accepted.
        drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            "origin",
        )
        .expect("the registered custodian must be allowed");

        // A different host claiming the same stream is refused.
        let err = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host2"),
            0,
            "origin",
        )
        .expect_err("a host that does not hold custody must fail closed");
        assert!(
            err.to_string().contains("custody"),
            "expected a custody refusal, got: {err}"
        );
    }

    #[test]
    fn drain_outbox_is_a_noop_when_empty() {
        let repo = init_repo();
        let coord1 = a("coord1");
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap()).unwrap(),
            short("host1"),
        )
        .unwrap();
        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
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
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();

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
            "origin",
        )
        .unwrap();
        assert_eq!(
            drained.published,
            vec![EventId::new(&coord1, 1), EventId::new(&coord1, 2)]
        );
        assert!(drained.rejected.is_empty());

        let (_header, log) = crate::stream::read_stream(repo.path(), &coord1).unwrap();
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
            "origin",
        )
        .unwrap();
        assert!(drained.rejected.is_empty());

        let (_header, log) = crate::stream::read_stream(repo.path(), &coord1).unwrap();
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
        let snap = crate::sync::cached_snapshot(repo.path(), repo.path()).unwrap();
        assert_eq!(snap.state.agents[&coord1].next_seq, 3);
    }

    /// Ported from the shipped version-one helper's identical `register`/
    /// `scope_set`/`issue_open` checks (`g-design:42`/`c-agent:15` on the
    /// live bus): a well-formed-but-nonexistent object id in `agent.
    /// registered.product_base`, `scope.set.base_code_commit`, or `issue.
    /// opened.code_commit` must be rejected here, since `apply.rs` never
    /// touches git and so cannot catch it -- v1 gained both checks after
    /// this v2 branch had already forked, a parity gap discovered while
    /// preparing this crate's own bus nomination (see `verify_object_ids_
    /// resolve`'s own doc comment).
    #[test]
    fn drain_outbox_rejects_a_well_formed_but_nonexistent_product_base() {
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
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
        crate::outbox::submit(
            repo.path(),
            "alice-reg",
            &Candidate::new(
                &alice,
                &EventData::AgentRegistered(crate::events::AgentRegistered {
                    display_name: short("Alice"),
                    primary_role: Role::Implementor,
                    purpose: text("x"),
                    product_base: Some(ObjectId::parse("f".repeat(40)).unwrap()),
                    product_branch: None,
                    provider: None,
                    model: None,
                }),
                vec![],
            ),
        )
        .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &alice,
            &short("host1"),
            0,
            "origin",
        )
        .unwrap();
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("product_base")
                && drained.rejected[0].reason.contains("does not resolve"),
            "{}",
            drained.rejected[0].reason
        );
    }

    #[test]
    fn drain_outbox_rejects_a_well_formed_but_nonexistent_base_code_commit() {
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
        )
        .unwrap();

        crate::outbox::submit(
            repo.path(),
            "scope-1",
            &Candidate::new(
                &coord1,
                &EventData::ScopeSet(crate::events::ScopeSet {
                    base_code_commit: ObjectId::parse("f".repeat(40)).unwrap(),
                    exclusive: crate::scalars::StringSet::default(),
                    shared: crate::scalars::StringSet::default(),
                    exports: crate::scalars::StringSet::default(),
                    depends_on: vec![],
                    note: text("x"),
                }),
                vec![],
            ),
        )
        .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            "origin",
        )
        .unwrap();
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("base_code_commit")
                && drained.rejected[0].reason.contains("does not resolve"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// The coordinator half of the same rule: `build_frontier` must choose
    /// the complete path for an audit report, and the report is therefore
    /// currency-sensitive. Asserted on the predicates directly, because the
    /// drain tests all supply a reachable remote and so cannot distinguish
    /// "complete was chosen" from "sparse happened to be enough".
    /// An audit report pins the revisions it inspected. A mistyped one makes
    /// the report read as authoritative about a commit that does not exist,
    /// which is the same silent failure the sibling tests above cover for
    /// `product_base`, `base_code_commit` and `code_commit`. `apply` already
    /// refuses a report naming a non-existent *issue*; this is the object-id
    /// half of the same rule, and it lives here because only the coordinator
    /// has the repository to resolve against.
    #[test]
    fn an_audit_report_is_frontier_complete_and_currency_sensitive() {
        let data = EventData::AuditReported(crate::events::AuditReported {
            inspected_commits: crate::scalars::StringSet::default(),
            areas: vec![text("coordination history")],
            methods: vec![text("replayed every stream")],
            limitations: vec![],
            issues: crate::scalars::StringSet::default(),
            summary: text("clean"),
        });
        assert!(
            requires_complete_frontier(&data),
            "the frontier is the report's only record of what it observed"
        );
        assert!(
            requires_synced_snapshot(&data),
            "an audit of an already-stale view is worth little"
        );
    }

    /// M2 from round 3: the gate-17 fetch can advance the registry past the
    /// epoch the frontier is built against.
    ///
    /// `registry_tip`/`epoch` are read before the fetch; `sync::synced_
    /// snapshot` then fetches `refs/heads/agent-registry` into that same
    /// local ref. Without re-reading, `build_frontier` builds a "complete"
    /// frontier for the *superseded* epoch, and `apply::require_complete_
    /// frontier` validates against whatever epoch the frontier names -- which
    /// reduction deliberately keeps in `known_epochs`. So the report would be
    /// accepted while omitting precisely the members the fetch just revealed:
    /// assurance without evidence, which is what requiring a complete
    /// frontier exists to prevent.
    ///
    /// Staged by advancing the registry on the *remote* only, then rewinding
    /// the local ref -- which is what a second host having registered someone
    /// looks like from here.
    /// The Critical from round 3: a frontier this host cannot build must
    /// reject one candidate, not poison the outbox forever.
    ///
    /// `build_frontier` was the only per-candidate failure in the drain loop
    /// that used `?`. When it fired, nothing was committed, nothing was
    /// removed from the outbox and no receipt was written -- and because the
    /// condition is a property of the *roster* rather than of the candidate,
    /// every later `coordinate` for that agent failed identically forever.
    /// No CLI command removes a pending candidate, so recovery meant
    /// hand-deleting the file.
    ///
    /// `audit.reported` is what makes it reachable in ordinary use: it is the
    /// only kind an ordinary agent publishes that needs a complete frontier,
    /// and `build_complete_frontier` fails whenever any active member has not
    /// yet published its stream root -- which `sync.rs` calls "a real,
    /// expected state, not an error".
    #[test]
    fn the_currency_fetch_advances_the_epoch_the_frontier_is_built_against() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let aud = a("aud");
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap()).unwrap(),
            short("host1"),
        )
        .unwrap();
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();

        let tip = crate::registry::read_registry_tip(repo.path())
            .unwrap()
            .unwrap();
        let epoch = crate::registry::read_epoch(repo.path(), &tip).unwrap();
        let mut members = epoch.active_members.clone();
        members.insert(
            aud.clone(),
            crate::registry::MemberBinding {
                role: Role::Auditor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
        crate::outbox::submit(
            repo.path(),
            "reg",
            &Candidate::new(
                &aud,
                &EventData::AgentRegistered(crate::events::AgentRegistered {
                    display_name: short("Auditor"),
                    primary_role: Role::Auditor,
                    purpose: text("auditor:whole-architecture"),
                    product_base: None,
                    product_branch: None,
                    provider: None,
                    model: None,
                }),
                vec![],
            ),
        )
        .unwrap();
        drain_outbox(repo.path(), repo.path(), &aud, &short("host1"), 0, &remote).unwrap();
        for r in [
            crate::registry::REGISTRY_REF.to_string(),
            crate::stream::stream_ref(&coord1).into_string(),
            crate::stream::stream_ref(&aud).into_string(),
        ] {
            let push = crate::gitrepo::run(repo.path(), &["push", &remote, &r]).unwrap();
            assert!(push.success, "{push:?}");
        }

        // The epoch this host currently knows, and will keep locally.
        let stale_tip = crate::registry::read_registry_tip(repo.path())
            .unwrap()
            .unwrap();

        // Another host registers `dave`: build the epoch, push it, then rewind
        // the local ref so only the remote has it.
        let epoch = crate::registry::read_epoch(repo.path(), &stale_tip).unwrap();
        let mut members = epoch.active_members.clone();
        members.insert(
            a("dave"),
            crate::registry::MemberBinding {
                role: Role::Implementor,
                host: short("host2"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
        let push = crate::gitrepo::run(
            repo.path(),
            &["push", &remote, crate::registry::REGISTRY_REF],
        )
        .unwrap();
        assert!(push.success, "{push:?}");
        crate::gitrepo::run(
            repo.path(),
            &[
                "update-ref",
                crate::registry::REGISTRY_REF,
                stale_tip.as_str(),
            ],
        )
        .unwrap();
        assert_eq!(
            crate::registry::read_registry_tip(repo.path())
                .unwrap()
                .unwrap(),
            stale_tip,
            "fixture: the local registry must be behind the remote"
        );

        crate::outbox::submit(
            repo.path(),
            "audit-1",
            &Candidate::new(
                &aud,
                &EventData::AuditReported(crate::events::AuditReported {
                    inspected_commits: crate::scalars::StringSet::default(),
                    areas: vec![text("coordination history")],
                    methods: vec![text("replayed every stream")],
                    limitations: vec![],
                    issues: crate::scalars::StringSet::default(),
                    summary: text("clean"),
                }),
                vec![],
            ),
        )
        .unwrap();

        let drained =
            drain_outbox(repo.path(), repo.path(), &aud, &short("host1"), 0, &remote).unwrap();

        // Built against the *fetched* epoch, `dave` is a member with no stream,
        // so the report is refused. Built against the stale one it would have
        // published, silently omitting `dave` from what it claims to have seen.
        assert!(
            drained.published.is_empty(),
            "the report must not publish against a superseded epoch: {drained:?}"
        );
        assert_eq!(drained.rejected.len(), 1, "{drained:?}");
        assert!(
            drained.rejected[0].reason.contains("dave"),
            "the refusal must name the member the fetch revealed: {}",
            drained.rejected[0].reason
        );
    }

    #[test]
    fn a_frontier_that_cannot_be_built_rejects_one_candidate_not_the_whole_drain() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let aud = a("aud");
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap()).unwrap(),
            short("host1"),
        )
        .unwrap();
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();

        // Register the auditor properly, so it has a stream root.
        let tip = crate::registry::read_registry_tip(repo.path())
            .unwrap()
            .unwrap();
        let epoch = crate::registry::read_epoch(repo.path(), &tip).unwrap();
        let mut members = epoch.active_members.clone();
        members.insert(
            aud.clone(),
            crate::registry::MemberBinding {
                role: Role::Auditor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
        crate::outbox::submit(
            repo.path(),
            "reg",
            &Candidate::new(
                &aud,
                &EventData::AgentRegistered(crate::events::AgentRegistered {
                    display_name: short("Auditor"),
                    primary_role: Role::Auditor,
                    purpose: text("auditor:whole-architecture"),
                    product_base: None,
                    product_branch: None,
                    provider: None,
                    model: None,
                }),
                vec![],
            ),
        )
        .unwrap();
        drain_outbox(repo.path(), repo.path(), &aud, &short("host1"), 0, &remote).unwrap();
        for r in [
            crate::registry::REGISTRY_REF.to_string(),
            crate::stream::stream_ref(&coord1).into_string(),
            crate::stream::stream_ref(&aud).into_string(),
        ] {
            let push = crate::gitrepo::run(repo.path(), &["push", &remote, &r]).unwrap();
            assert!(push.success, "{push:?}");
        }

        // Now a member the roster knows and no stream exists for -- the state
        // `sync.rs` calls expected.
        let tip = crate::registry::read_registry_tip(repo.path())
            .unwrap()
            .unwrap();
        let epoch = crate::registry::read_epoch(repo.path(), &tip).unwrap();
        let mut members = epoch.active_members.clone();
        members.insert(
            a("dave"),
            crate::registry::MemberBinding {
                role: Role::Implementor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
        let push = crate::gitrepo::run(
            repo.path(),
            &["push", &remote, crate::registry::REGISTRY_REF],
        )
        .unwrap();
        assert!(push.success, "{push:?}");

        // An audit report (needs the complete frontier) plus an ordinary
        // candidate that does not.
        crate::outbox::submit(
            repo.path(),
            "audit-1",
            &Candidate::new(
                &aud,
                &EventData::AuditReported(crate::events::AuditReported {
                    inspected_commits: crate::scalars::StringSet::default(),
                    areas: vec![text("coordination history")],
                    methods: vec![text("replayed every stream")],
                    limitations: vec![],
                    issues: crate::scalars::StringSet::default(),
                    summary: text("clean"),
                }),
                vec![],
            ),
        )
        .unwrap();
        crate::outbox::submit(repo.path(), "note", &status_candidate(&aud, "still here")).unwrap();

        let drained =
            drain_outbox(repo.path(), repo.path(), &aud, &short("host1"), 0, &remote).unwrap();

        // The audit is rejected, with a durable receipt naming the cause ...
        assert_eq!(drained.rejected.len(), 1, "{drained:?}");
        assert_eq!(drained.rejected[0].kind, "audit.reported");
        assert!(
            drained.rejected[0].reason.contains("complete frontier"),
            "{}",
            drained.rejected[0].reason
        );
        // ... and the unrelated candidate behind it still publishes.
        assert!(!drained.published.is_empty(), "{drained:?}");

        // The outbox is drained, not wedged: a second run has nothing left.
        let again =
            drain_outbox(repo.path(), repo.path(), &aud, &short("host1"), 0, &remote).unwrap();
        assert!(
            again.published.is_empty() && again.rejected.is_empty(),
            "{again:?}"
        );
    }

    #[test]
    fn drain_outbox_rejects_an_audit_report_pinning_a_nonexistent_commit() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let aud = a("aud");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
        )
        .unwrap();
        // The auditor must be a member of the current epoch for
        // `authorize_stream_write` to let its outbox be drained at all.
        let tip = crate::registry::read_registry_tip(repo.path())
            .unwrap()
            .unwrap();
        let epoch = crate::registry::read_epoch(repo.path(), &tip).unwrap();
        let mut members = epoch.active_members.clone();
        members.insert(
            aud.clone(),
            crate::registry::MemberBinding {
                role: Role::Auditor,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();

        // The auditor needs a published stream root before it can build the
        // complete frontier an `audit.reported` now requires -- every active
        // member must have a stream for `build_complete_frontier` to name it.
        crate::outbox::submit(
            repo.path(),
            "reg",
            &Candidate::new(
                &aud,
                &EventData::AgentRegistered(crate::events::AgentRegistered {
                    display_name: short("C Auditor"),
                    primary_role: Role::Auditor,
                    purpose: text("auditor:whole-architecture"),
                    product_base: None,
                    product_branch: None,
                    provider: None,
                    model: None,
                }),
                vec![],
            ),
        )
        .unwrap();
        // A reachable remote, because an `audit.reported` requires a complete
        // frontier and is therefore currency-sensitive: the drain probes the
        // remote before publishing one. Without this the candidate is refused
        // for gate 17 rather than for the object id under test.
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();
        let registered =
            drain_outbox(repo.path(), repo.path(), &aud, &short("host1"), 0, &remote).unwrap();
        assert_eq!(registered.rejected.len(), 0, "{registered:?}");
        for r in [
            crate::registry::REGISTRY_REF.to_string(),
            crate::stream::stream_ref(&coord1).into_string(),
            crate::stream::stream_ref(&aud).into_string(),
        ] {
            let push = crate::gitrepo::run(repo.path(), &["push", &remote, &r]).unwrap();
            assert!(push.success, "{push:?}");
        }

        crate::outbox::submit(
            repo.path(),
            "audit-1",
            &Candidate::new(
                &aud,
                &EventData::AuditReported(crate::events::AuditReported {
                    inspected_commits: crate::scalars::StringSet::from_iter([ObjectId::parse(
                        "f".repeat(40),
                    )
                    .unwrap()]),
                    areas: vec![text("coordination history")],
                    methods: vec![text("replayed every stream")],
                    limitations: vec![],
                    issues: crate::scalars::StringSet::default(),
                    summary: text("s"),
                }),
                vec![],
            ),
        )
        .unwrap();

        let drained =
            drain_outbox(repo.path(), repo.path(), &aud, &short("host1"), 0, &remote).unwrap();
        assert!(drained.published.is_empty(), "{drained:?}");
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("inspected_commits")
                && drained.rejected[0].reason.contains("does not resolve"),
            "{}",
            drained.rejected[0].reason
        );
    }

    #[test]
    fn drain_outbox_rejects_a_well_formed_but_nonexistent_issue_code_commit() {
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
        )
        .unwrap();

        crate::outbox::submit(
            repo.path(),
            "issue-1",
            &Candidate::new(
                &coord1,
                &EventData::IssueOpened(crate::events::IssueOpened {
                    target: coord1.clone(),
                    issue_kind: crate::events::IssueKind::Bug,
                    severity: crate::common::Priority::Normal,
                    summary: text("s"),
                    code_commit: Some(ObjectId::parse("f".repeat(40)).unwrap()),
                    locations: vec![],
                    expected: None,
                    observed_behavior: None,
                    reproduction: vec![],
                    blocks: crate::scalars::StringSet::default(),
                    evidence: crate::scalars::StringSet::default(),
                }),
                vec![],
            ),
        )
        .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            "origin",
        )
        .unwrap();
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0].reason.contains("code_commit")
                && drained.rejected[0].reason.contains("does not resolve"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// A reference to an event id that does not exist is refused at
    /// submission, which is the only place it can be refused at all.
    ///
    /// This is the other half of the `e-auditor:10` outage. That event cited
    /// `c-reviewer:100`, one past that stream's tip; `build_frontier` took
    /// `through` from whatever the caller referenced and never checked the
    /// id named anything (there was a TODO here saying exactly that), so it
    /// published. Every host then failed to reduce the bus, and the log
    /// being append-only meant nothing could withdraw it.
    ///
    /// The reducer now tolerates such a reference, so the fleet survives one
    /// -- but tolerating it is damage control. Here the candidate is still
    /// in the author's outbox, so refusing costs a durable receipt and a
    /// retry rather than the fleet.
    #[test]
    fn drain_outbox_rejects_a_reference_to_an_event_that_does_not_exist() {
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
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
        crate::outbox::submit(
            repo.path(),
            "alice-reg",
            &Candidate::new(
                &alice,
                &EventData::AgentRegistered(crate::events::AgentRegistered {
                    display_name: short("alice"),
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
            "origin",
        )
        .unwrap();

        // alice's stream is exactly its root, `alice:0`. Citing `alice:7` is
        // the live shape: a well-formed id, for a real agent, naming nothing.
        crate::outbox::submit(
            repo.path(),
            "cites-a-ghost",
            &Candidate::new(
                &coord1,
                &EventData::IssueOpened(crate::events::IssueOpened {
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
                    evidence: crate::scalars::StringSet::from_iter([EventId::new(&alice, 7)]),
                }),
                vec![],
            ),
        )
        .unwrap();

        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            "origin",
        )
        .unwrap();
        assert!(drained.published.is_empty(), "{drained:?}");
        assert_eq!(drained.rejected.len(), 1, "{drained:?}");
        let reason = &drained.rejected[0].reason;
        assert!(
            reason.contains("alice:7") && reason.contains("does not exist"),
            "the receipt must name the ghost and where the stream really ends: {reason}"
        );
        assert!(
            reason.contains("alice:0"),
            "and it must say where the stream really ends, so the author can correct it: {reason}"
        );
    }

    /// Gate 17 at the *call site*, for the clause that only reassignments
    /// reach.
    ///
    /// `reassignments_require_a_synced_snapshot_...` pins the predicate's
    /// truth table; mutation testing showed that was not enough. Replacing
    /// either `requires_synced_snapshot` call in `drain_outbox` with
    /// `requires_complete_frontier` -- the same weakening as deleting the
    /// clause -- left every suite green, so a reassignment could silently
    /// stop demanding a fresh cut.
    ///
    /// The assertion is on the *reason*, not merely on rejection: with the
    /// clause gone the candidate is still rejected, but for an unrelated
    /// downstream cause, and only the gate-17 wording distinguishes the two.
    /// Gate 17 (AGENT_COORDINATION_EVOLUTION.md section 2.4): a
    /// currency-sensitive candidate (here, `schema.activated`) must be
    /// refused, not validated against a stale cached cut, when the fresh
    /// remote probe itself fails -- while an ordinary candidate in the same
    /// batch is unaffected, since only the currency-sensitive one actually
    /// needs that fresher view.
    #[test]
    fn drain_outbox_fails_closed_on_a_reassignment_when_the_fetch_fails() {
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
        )
        .unwrap();

        let reassign = crate::outbox::Candidate::new(
            &coord1,
            &EventData::IssueReassigned(crate::events::IssueReassigned {
                issue: EventId::new(&a("alice"), 1),
                previous_assignment: EventId::new(&a("alice"), 2),
                previous_target: a("bob"),
                new_target: a("carol"),
                reason: text("bob went quiet"),
            }),
            vec![],
        );
        crate::outbox::submit(repo.path(), "reassign", &reassign).unwrap();

        // No "origin" remote exists, so the currency probe cannot succeed.
        let drained = drain_outbox(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            "origin",
        )
        .unwrap();

        assert!(drained.published.is_empty(), "{drained:?}");
        assert_eq!(drained.rejected.len(), 1);
        assert_eq!(drained.rejected[0].kind, "issue.reassigned");
        assert!(
            drained.rejected[0].reason.contains("gate 17"),
            "a reassignment must fail closed on the currency probe, not on some later check: {}",
            drained.rejected[0].reason
        );
    }

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
        )
        .unwrap();
        crate::outbox::submit(repo.path(), "client-1", &status_candidate(&coord1, "hi")).unwrap();

        let (drained, receipt) = drain_and_publish(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
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
        let coord1 = a("coord1");
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            ObjectId::parse(crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap()).unwrap(),
            short("host1"),
        )
        .unwrap();
        let (drained, receipt) = drain_and_publish(
            repo.path(),
            repo.path(),
            &coord1,
            &short("host1"),
            0,
            &origin.path().to_string_lossy(),
        )
        .unwrap();
        assert!(drained.published.is_empty());
        assert!(drained.rejected.is_empty());
        // The bus exists now (custody has to be authorizable for the drain to
        // be reached at all), so the coordinator's own stream root does get
        // published -- that is the *publish* half doing its job. What this
        // test is about is the drain half: an empty outbox contributes no new
        // events, and nothing is rejected.
        assert!(
            receipt.rejected.is_empty(),
            "nothing should be rejected: {receipt:?}"
        );
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
        let new_epoch = crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
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
        crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();
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
        let (_header, log) = crate::stream::read_stream(repo.path(), &alice).unwrap();
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
        let new_epoch = crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();

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
            drain_outbox(repo.path(), repo.path(), ag, &short("host1"), 0, &remote).unwrap();
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
        // Published like any real candidate: authorship is checked *after*
        // the candidate tag is confirmed and fetched, so that a coordinator
        // draining from a checkout which has only ever seen `main` and the
        // bus still has the reviewed commits to read trailers from.
        publish_candidate_tag(&f, &candidate);
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
        publish_candidate_tag(&f, &candidate);
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
        publish_candidate_tag(&f, &candidate);
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

    /// Tags `commit` as `reviewer`'s candidate and pushes the tag, exactly
    /// as `prepare-merge` would -- so the gate under test sees a candidate
    /// that is published and fetchable, and can only reject it for what the
    /// *object* says.
    fn publish_candidate_tag(f: &ReviewFixture, commit: &str) {
        let tag = crate::merge_candidate::candidate_tag_name(&f.reviewer, commit);
        crate::gitrepo::tag_lightweight(f.repo.path(), &tag, commit).unwrap();
        let push = crate::gitrepo::run(
            f.repo.path(),
            &["push", &f.remote, &format!("refs/tags/{tag}")],
        )
        .unwrap();
        assert!(push.success, "{push:?}");
    }

    /// A commit with the given parents, message and tree, built directly --
    /// not through `merge_candidate::reconstruct_candidate`. This is how a
    /// tampered or hand-crafted candidate gets into the fixture: the gate
    /// no longer rebuilds the merge, so what it rejects has to be a real
    /// object that is wrong in a specific, nameable way.
    fn forged_candidate(
        f: &ReviewFixture,
        parents: &[&str],
        message: &str,
        tree_of: &str,
    ) -> String {
        use crate::gitobjects::{HistoryReader, ObjectWriter};
        let g = crate::gitobjects::Libgit2Reader::open(f.repo.path()).unwrap();
        let tree = g
            .resolve_rev(&format!("{tree_of}^{{tree}}"))
            .unwrap()
            .expect("tree must resolve");
        let resolved: Vec<ObjectId> = parents
            .iter()
            .map(|p| g.resolve_rev(p).unwrap().expect("parent must resolve"))
            .collect();
        let refs: Vec<&ObjectId> = resolved.iter().collect();
        g.create_commit(&tree, &refs, message)
            .unwrap()
            .into_string()
    }

    /// The publication gate used to rebuild the merge with this host's own
    /// `git merge-tree --write-tree` and compare object ids, which is what
    /// made an installed git version protocol authority (g-design:249). It
    /// now validates the object the candidate tag actually names -- so a
    /// forged candidate has to be rejected by a property of *that object*,
    /// not by a hash it fails to match.
    ///
    /// Parents first: a commit that merges the right two commits in the
    /// wrong order is a different merge.
    #[test]
    fn drain_outbox_rejects_review_merge_authorized_whose_candidate_has_the_wrong_parents() {
        let f = build_review_fixture(Some("zoe"));
        let forged = forged_candidate(
            &f,
            // Reversed: `reviewed_commit` first, `previous_main` second.
            &[&f.feature_commit, &f.previous_main],
            &format!(
                "agent-bus candidate\n\nAgent-Bus-Reviewer: {}\n",
                f.reviewer
            ),
            &f.feature_commit,
        );
        publish_candidate_tag(&f, &forged);
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &forged),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("candidate parents do not match"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// A candidate whose parents are right but which carries somebody
    /// else's reviewer trailer. Nobody rebuilds the tree any more, so this
    /// trailer is the accountability binding: it says which reviewer stands
    /// behind the content.
    #[test]
    fn drain_outbox_rejects_review_merge_authorized_whose_candidate_names_another_reviewer() {
        let f = build_review_fixture(Some("zoe"));
        let forged = forged_candidate(
            &f,
            &[&f.previous_main, &f.feature_commit],
            "agent-bus candidate\n\nAgent-Bus-Reviewer: someone-else\n",
            &f.feature_commit,
        );
        publish_candidate_tag(&f, &forged);
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &forged),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("exactly one matching Agent-Bus-Reviewer trailer"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// Right parents, right reviewer trailer, but extra content in the
    /// message. The exact-message check is what stops a candidate from
    /// smuggling further trailers past a validator that only reads back the
    /// one it expects.
    #[test]
    fn drain_outbox_rejects_review_merge_authorized_whose_candidate_message_carries_more_than_the_trailer(
    ) {
        let f = build_review_fixture(Some("zoe"));
        let forged = forged_candidate(
            &f,
            &[&f.previous_main, &f.feature_commit],
            &format!(
                "agent-bus candidate\n\nAgent-Bus-Reviewer: {}\nAgent-Bus-Agent: {}\n",
                f.reviewer, f.reviewer
            ),
            &f.feature_commit,
        );
        publish_candidate_tag(&f, &forged);
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &forged),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("does not carry the exact candidate message"),
            "{}",
            drained.rejected[0].reason
        );
    }

    /// The content bound, and the check that most directly replaces the
    /// deleted reconstruction: a candidate whose parents, message and
    /// trailer are all correct, but whose *tree* carries a file the
    /// nomination never covered.
    ///
    /// Under the old design this was caught only incidentally -- the tree
    /// differed from the local rebuild, so the object ids differed. There
    /// is no rebuild now, so scope is what bounds the tree, and this test
    /// fails outright if `verify_candidate_scope` is not called here.
    #[test]
    fn drain_outbox_rejects_review_merge_authorized_whose_candidate_touches_an_unreviewed_path() {
        let f = build_review_fixture(Some("zoe"));
        // A commit on top of the feature branch touching a path outside the
        // reviewed scope (`feature.txt`), used only for its tree.
        git(
            f.repo.path(),
            &["checkout", "--quiet", "--detach", &f.feature_commit],
        );
        std::fs::write(f.repo.path().join("smuggled.txt"), "not reviewed\n").unwrap();
        git(f.repo.path(), &["add", "."]);
        git(
            f.repo.path(),
            &["commit", "-q", "-m", "smuggled\n\nAgent-Bus-Agent: zoe"],
        );
        let smuggled = crate::gitrepo::rev_parse(f.repo.path(), "HEAD").unwrap();
        git(f.repo.path(), &["checkout", "--quiet", "main"]);

        let forged = forged_candidate(
            &f,
            &[&f.previous_main, &f.feature_commit],
            &format!(
                "agent-bus candidate\n\nAgent-Bus-Reviewer: {}\n",
                f.reviewer
            ),
            &smuggled,
        );
        publish_candidate_tag(&f, &forged);
        crate::outbox::submit(
            f.repo.path(),
            "auth",
            &merge_authorized_candidate(&f, &forged),
        )
        .unwrap();

        let drained = drain_reviewer(&f);
        assert!(drained.published.is_empty());
        assert_eq!(drained.rejected.len(), 1);
        assert!(
            drained.rejected[0]
                .reason
                .contains("outside reviewed_scope"),
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

    /// The currency half of the `merge_engine_epoch` rule, in its new home.
    ///
    /// `apply` checks only that the epoch names a real activation, because
    /// that is all reduction can soundly do: the authorization references
    /// the epoch it names, so that one is always applied first, but a
    /// *later* `merge_engine.activated` moves the selection and this event
    /// neither references nor need have observed it. Asking there made the
    /// same two events reduce on a host that replayed the authorization
    /// first and fail on one that replayed the activation first.
    ///
    /// Here there is no replay order: `state` is the publishing host's own
    /// fully-reduced view. Without this test the currency rule would have
    /// been deleted rather than moved --
    /// `a_superseded_merge_engine_epoch_still_reduces` asserts reduction
    /// accepts exactly what this refuses, and one of the pair alone would
    /// look like a regression.
    #[test]
    fn the_authorization_gate_refuses_a_stale_merge_engine_epoch() {
        let f = build_review_fixture(Some("zoe"));
        let candidate = crate::merge_candidate::reconstruct_candidate(
            f.repo.path(),
            &f.previous_main,
            &f.feature_commit,
            &f.reviewer,
        )
        .unwrap();
        // Everything else about this candidate is genuinely valid, so the
        // gate reaches its last check rather than stopping earlier.
        let tag = crate::merge_candidate::candidate_tag_name(&f.reviewer, &candidate);
        crate::gitrepo::tag_lightweight(f.repo.path(), &tag, &candidate).unwrap();
        let push = crate::gitrepo::run(
            f.repo.path(),
            &["push", &f.remote, &format!("refs/tags/{tag}")],
        )
        .unwrap();
        assert!(push.success, "{push:?}");

        let snapshot =
            crate::sync::cached_snapshot(f.repo.path(), f.repo.path()).expect("reduce fixture");
        let mut state = snapshot.state;

        let d = match merge_authorized_candidate(&f, &candidate)
            .typed_data()
            .unwrap()
        {
            EventData::ReviewMergeAuthorized(d) => d,
            other => panic!("fixture built the wrong event: {other:?}"),
        };

        // The epoch the authorization names is real, so nothing else in the
        // gate objects to it -- but the bus has since selected a different
        // one. Both epochs record an engine version no host anywhere runs,
        // which is now simply ignored: if any comparison against the
        // installed git ever comes back, this test stops reaching the
        // stale-epoch refusal it is about and fails.
        let newer = EventId::new(&f.coord1, 4242);
        let engine_version = short(FOREIGN_ENGINE_VERSION);
        state.merge_engine_info.insert(
            d.merge_engine_epoch.clone(),
            (
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                engine_version.clone(),
            ),
        );
        state.merge_engine_info.insert(
            newer.clone(),
            (
                short(crate::bootstrap::SUPPORTED_MERGE_ENGINE),
                engine_version,
            ),
        );
        state.current_merge_engine_epoch = Some(newer.clone());

        let err = verify_review_merge_authorized(f.repo.path(), &f.remote, &state, &f.reviewer, &d)
            .expect_err("an authorization pinned to a superseded engine must not publish");
        let msg = err.to_string();
        assert!(
            msg.contains("is not the currently selected merge engine epoch")
                && msg.contains(&newer.to_string()),
            "the message must name the epoch that is current now: {msg}"
        );
    }

    /// Everything this gate itself checks is genuinely valid: real
    /// authorship, a candidate that matches the deterministic
    /// reconstruction exactly, and a tag both local and pushed to `remote`.
    /// This crate has no production path yet that can populate
    /// `current_merge_engine_epoch` (see `merge_authorized_candidate`'s own
    /// comment) -- a real, separate, pre-existing gap this task does not
    /// fix -- so full end-to-end acceptance is not yet reachable. What this
    /// test instead proves is that this gate's own substantive checks did
    /// not reject the candidate: the rejection that surfaces is the known
    /// unrelated `merge_engine_epoch` currency failure, and none of the
    /// authorship, reconstruction or candidate-tag text appears.
    ///
    /// That currency check now lives in this gate too (it cannot live in
    /// `apply`, which has no sound way to ask it), so it is deliberately
    /// absent from the exclusion list below.
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
            "candidate parents do not match",
            "exactly one matching Agent-Bus-Reviewer trailer",
            "does not carry the exact candidate message",
            "outside reviewed_scope",
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
            "candidate parents do not match",
            "exactly one matching Agent-Bus-Reviewer trailer",
            "does not carry the exact candidate message",
            "outside reviewed_scope",
            "candidate tag is not fetchable",
            "is not fetchable from",
        ] {
            assert!(
                !reason.contains(this_gates_own_text),
                "rejection should not come from verify_review_merge_authorized, got: {reason}"
            );
        }
    }

    /// Gate 17 for a broadcast whose audience resolves against mutable
    /// state, and the reason the predicate cannot simply defer to
    /// `requires_complete_frontier`.
    ///
    /// An informational `TopicSubscribers` broadcast needs no complete
    /// frontier, so before this it was validated against whatever cached cut
    /// `drain_outbox` happened to hold. `verify_broadcast_published` is now
    /// the *only* place gate 12's exactness is checked -- reduction has no
    /// sound way to ask it -- so a stale cut there means the single check
    /// can accept a snapshot that omits a subscriber who has already
    /// published remotely, and reduction then records the wrong audience
    /// with no later synchronization able to repair it.
    #[test]
    fn a_mutable_selector_broadcast_requires_a_synced_snapshot_without_a_complete_frontier() {
        let (_state, epoch) = state_with_subscribers(&[("alice", Role::Implementor, &[])]);
        let informational =
            EventData::BroadcastPublished(broadcast_to_subscribers(&epoch, &["alice"]));
        assert!(
            requires_synced_snapshot(&informational),
            "a mutable-selector broadcast must demand a fresh cut"
        );
        assert!(
            !requires_complete_frontier(&informational),
            "fixture: if this ever needs a complete frontier the first clause would satisfy the assertion above and it would stop testing anything"
        );

        // And the narrowing is real: a selector that reads only the pinned
        // epoch is not made currency-sensitive by this rule.
        let mut immutable = broadcast_to_subscribers(&epoch, &["alice"]);
        immutable.audience_selector = crate::common::AudienceSelector::Agents(
            crate::scalars::StringSet::from_iter([a("alice")]),
        );
        let immutable = EventData::BroadcastPublished(immutable);
        assert!(
            !requires_synced_snapshot(&immutable),
            "an explicit-list selector resolves from the pinned epoch and needs no fresh cut"
        );
    }

    /// The predicate above is only worth anything if `drain_outbox` actually
    /// calls `verify_broadcast_published`. This drives the whole path and
    /// fails if that call site is deleted.
    ///
    /// A subscription is published to the remote *after* this checkout's
    /// cached snapshot was taken, so a snapshot that names only the
    /// previously-known subscriber is stale-correct and fresh-wrong. Gate 17
    /// forces the fresh cut; gate 12 then rejects it.
    #[test]
    fn drain_outbox_rejects_a_broadcast_whose_audience_went_stale_on_the_remote() {
        let f = build_two_host_broadcast_fixture();

        // alice publishes to release.main subscribers, naming only bob --
        // true when alice last synced, false now that carol has subscribed
        // on the other host.
        crate::outbox::submit(f.alice_repo.path(), "bcast", &f.broadcast_naming(&["bob"])).unwrap();
        let drained = drain_outbox(
            f.alice_repo.path(),
            f.alice_repo.path(),
            &a("alice"),
            &short("host-a"),
            0,
            &f.remote,
        )
        .expect("draining must not error, it must reject the candidate");
        assert!(drained.published.is_empty(), "{drained:?}");
        assert_eq!(drained.rejected.len(), 1, "{drained:?}");
        let reason = &drained.rejected[0].reason;
        assert!(
            reason.contains("audience_snapshot does not match") && reason.contains("carol"),
            "the stale snapshot must be refused, naming who was missed: {reason}"
        );

        // The exact current audience is accepted.
        crate::outbox::submit(
            f.alice_repo.path(),
            "bcast2",
            &f.broadcast_naming(&["bob", "carol"]),
        )
        .unwrap();
        let drained = drain_outbox(
            f.alice_repo.path(),
            f.alice_repo.path(),
            &a("alice"),
            &short("host-a"),
            0,
            &f.remote,
        )
        .expect("the current snapshot publishes");
        assert!(
            drained.rejected.is_empty(),
            "the exact current audience must publish: {drained:?}"
        );
        assert!(!drained.published.is_empty(), "{drained:?}");
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
            merge_engine_version: FOREIGN_ENGINE_VERSION.to_string(),
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

    /// Pushes `dir`'s current `main` to a fresh bare origin and returns it
    /// (caller must keep the `TempDir` alive for as long as `remote` is
    /// used) -- `verify_review_merge_reconciled` fetches `main` from
    /// `remote` rather than trusting `dir`'s own local `refs/heads/main`
    /// (round-6 review), so every test exercising the live-Git branch below
    /// needs a real remote to fetch from, not just a local ref.
    fn push_main_to_a_fresh_origin(dir: &Path) -> (tempfile::TempDir, String) {
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();
        let push = crate::gitrepo::run(dir, &["push", &remote, "refs/heads/main"]).unwrap();
        assert!(push.success, "{push:?}");
        (origin, remote)
    }

    /// Two checkouts sharing one origin: alice publishes from `alice_repo`,
    /// and carol's `subscription.set` reaches the origin from a *second*
    /// clone that alice has never fetched.
    ///
    /// Deliberately two real repositories. Several critical defects in this
    /// crate were invisible to single-repository tests, and "alice's cached
    /// view is behind the remote" is precisely the condition that cannot be
    /// simulated inside one clone.
    struct TwoHostBroadcast {
        alice_repo: tempfile::TempDir,
        #[allow(dead_code)]
        other_repo: tempfile::TempDir,
        #[allow(dead_code)]
        origin: tempfile::TempDir,
        remote: String,
        epoch_id: ObjectId,
    }

    impl TwoHostBroadcast {
        fn broadcast_naming(&self, snapshot: &[&str]) -> Candidate {
            let mut d = broadcast_to_subscribers_with_epoch(&self.epoch_id, snapshot);
            d.summary = short("release cut");
            Candidate::new(&a("alice"), &EventData::BroadcastPublished(d), vec![])
        }
    }

    fn broadcast_to_subscribers_with_epoch(
        epoch_id: &ObjectId,
        snapshot: &[&str],
    ) -> crate::events::BroadcastPublished {
        crate::events::BroadcastPublished {
            topics: crate::scalars::StringSet::from_iter([
                crate::scalars::CoordinationTopic::parse("release.main".into()).unwrap(),
            ]),
            importance: crate::common::Importance::Informational,
            summary: short("s"),
            detail: text("d"),
            affected_paths: crate::scalars::StringSet::default(),
            affected_interfaces: crate::scalars::StringSet::default(),
            product_commits: crate::scalars::StringSet::default(),
            audience_selector: crate::common::AudienceSelector::TopicSubscribers(
                crate::scalars::CoordinationTopic::parse("release.main".into()).unwrap(),
            ),
            audience_epoch: epoch_id.clone(),
            audience_snapshot: crate::scalars::StringSet::from_iter(snapshot.iter().map(|n| a(n))),
            acknowledgement: crate::common::AckRequirement::None,
            deadline: None,
            supersedes: crate::scalars::StringSet::default(),
            workaround: None,
            expiry_condition: None,
        }
    }

    fn build_two_host_broadcast_fixture() -> TwoHostBroadcast {
        use crate::events::AgentRegistered;
        use crate::registry::MemberBinding;

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
            short("host-a"),
        )
        .unwrap();

        let mut members = epoch.active_members.clone();
        for name in ["alice", "bob", "carol"] {
            members.insert(
                a(name),
                MemberBinding {
                    role: Role::Implementor,
                    host: short("host-a"),
                    coordinator_custody_epoch: 0,
                    standby: None,
                },
            );
        }
        let epoch = crate::registry::propose_transition(repo.path(), &epoch, members).unwrap();

        for name in ["alice", "bob", "carol"] {
            let ag = a(name);
            crate::outbox::submit(
                repo.path(),
                &format!("{ag}-reg"),
                &Candidate::new(
                    &ag,
                    &EventData::AgentRegistered(AgentRegistered {
                        display_name: short(name),
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
            // `drain_outbox` alone only writes local refs; the origin is
            // what the second checkout clones from.
            let (drained, receipt) =
                drain_and_publish(repo.path(), repo.path(), &ag, &short("host-a"), 0, &remote)
                    .unwrap();
            assert!(drained.rejected.is_empty(), "{drained:?}");
            assert!(receipt.rejected.is_empty(), "{receipt:?}");
        }

        // bob subscribes, and alice sees it.
        let subscribe = |repo: &Path, who: &Agent, host: &str| {
            crate::outbox::submit(
                repo,
                &format!("{who}-sub"),
                &Candidate::new(
                    who,
                    &EventData::SubscriptionSet(crate::events::SubscriptionSet {
                        topics: crate::scalars::StringSet::from_iter([
                            crate::scalars::CoordinationTopic::parse("release.main".into())
                                .unwrap(),
                        ]),
                    }),
                    vec![],
                ),
            )
            .unwrap();
            let (drained, receipt) =
                drain_and_publish(repo, repo, who, &short(host), 0, &remote).unwrap();
            assert!(drained.rejected.is_empty(), "{drained:?}");
            assert!(receipt.rejected.is_empty(), "{receipt:?}");
        };
        subscribe(repo.path(), &a("bob"), "host-a");

        // The registry has to reach the origin before a second checkout can
        // read it; publishing a stream only pushes that stream's own ref.
        let push = crate::gitrepo::run(
            repo.path(),
            &[
                "push",
                &remote,
                "+refs/heads/agent-registry:refs/heads/agent-registry",
            ],
        )
        .unwrap();
        assert!(push.success, "{push:?}");

        // A second checkout of the same origin. carol subscribes from there,
        // so the subscription exists on the remote and nowhere in `repo` --
        // which is the condition a single-repository test cannot create, and
        // exactly the one this whole fix is about.
        let other = tempfile::tempdir().unwrap();
        let clone = std::process::Command::new("git")
            .args(["clone", "--quiet", &remote])
            .arg(other.path().join("wc"))
            .status()
            .unwrap();
        assert!(clone.success());
        let other_wc = other.path().join("wc");
        let fetch =
            crate::gitrepo::run(&other_wc, &["fetch", &remote, "+refs/heads/*:refs/heads/*"])
                .unwrap();
        assert!(fetch.success, "{fetch:?}");
        subscribe(&other_wc, &a("carol"), "host-a");

        TwoHostBroadcast {
            alice_repo: repo,
            other_repo: other,
            origin,
            remote,
            epoch_id: epoch.id.clone(),
        }
    }

    /// AGENT_COORDINATION_EVOLUTION.md's currency rule (gate 17): a
    /// reassignment must be published against a *freshly synced* snapshot,
    /// because it moves work between agents and a stale read can hand the
    /// same item to two of them. That is a strictly wider set than the
    /// events needing a *complete frontier*, and the second clause of
    /// `requires_synced_snapshot` is the only thing expressing it -- deleting
    /// it left the whole suite green.
    #[test]
    fn reassignments_require_a_synced_snapshot_even_though_they_need_no_complete_frontier() {
        let reassign = crate::events::EventData::IssueReassigned(crate::events::IssueReassigned {
            issue: EventId::new(&a("alice"), 1),
            previous_assignment: EventId::new(&a("alice"), 2),
            previous_target: a("bob"),
            new_target: a("carol"),
            reason: text("moving it"),
        });
        assert!(
            requires_synced_snapshot(&reassign),
            "a reassignment must demand a fresh cut"
        );
        assert!(
            !requires_complete_frontier(&reassign),
            "fixture: if this ever needs a complete frontier, the first clause would satisfy the assertion above and it would stop testing anything"
        );
    }

    /// `through` names the last sequence a member has actually published,
    /// which for a log of `n` events is `n - 1`. Off-by-one here would make
    /// every complete frontier claim an event that does not exist yet, and
    /// no test asserted the value -- only that a frontier could be built.
    #[test]
    fn a_complete_frontier_names_the_last_published_sequence_not_the_next_one() {
        let dir = init_repo();
        let coord = a("coord1");
        crate::bootstrap::genesis(
            dir.path(),
            &coord,
            crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
            crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
            "sha1".to_string(),
            crate::scalars::ObjectId::parse(crate::gitrepo::rev_parse(dir.path(), "HEAD").unwrap())
                .unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
        )
        .unwrap();

        let tip = crate::registry::read_registry_tip(dir.path())
            .unwrap()
            .unwrap();
        let epoch = crate::registry::read_epoch(dir.path(), &tip).unwrap();
        let frontier = build_complete_frontier(dir.path(), &epoch).unwrap();

        let reader = crate::gitobjects::Libgit2Reader::open(dir.path()).unwrap();
        // Explicit, so the loop below cannot become vacuous by the frontier
        // turning up empty. `ObservedFrontier::complete` would reject that
        // today, which makes this indirect rather than absent -- and indirect
        // protection is the kind that quietly stops holding.
        assert!(
            !frontier.entries.is_empty(),
            "a complete frontier must name at least the coordinator"
        );
        for entry in frontier.entries.values() {
            let stream_tip = crate::stream::read_stream_tip(dir.path(), &entry.agent)
                .unwrap()
                .unwrap();
            let published =
                crate::storage::read_stream_log_at(&reader, &stream_tip, &entry.agent).unwrap();
            assert_eq!(
                entry.through.seq(),
                published.len() as u64 - 1,
                "through must name the last published sequence for {}",
                entry.agent
            );
            assert!(
                published.iter().any(|e| e.id == entry.through),
                "through must name an event that actually exists"
            );
        }
    }

    /// A reconciliation is verified against `main` *as the remote has it*.
    /// If that fetch cannot run, the check has no ground truth and must fail
    /// closed -- accepting on an unreachable remote would let a reconciliation
    /// claiming any `main_commit` through unverified.
    #[test]
    fn verify_review_merge_reconciled_fails_closed_when_main_cannot_be_fetched() {
        let dir = init_repo();
        let previous_main = crate::gitrepo::rev_parse(dir.path(), "main").unwrap();
        let next = author_commit_for_reconcile(dir.path(), &previous_main, "feature.txt");
        git(dir.path(), &["update-ref", "refs/heads/main", &next]);
        let (state, auth_id) = state_with_bare_authorization(&previous_main, &next, &next);
        let d = reconciled_data(&auth_id, &previous_main, &next, &next);

        // A remote that cannot be contacted at all.
        let unreachable = dir.path().join("no-such-origin.git");
        let err = verify_review_merge_reconciled(
            dir.path(),
            &unreachable.display().to_string(),
            &state,
            &d,
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("could not fetch refs/heads/main"),
            "an unreachable remote must fail closed, got: {err}"
        );
    }

    #[test]
    fn verify_review_merge_reconciled_rejects_when_main_was_never_advanced() {
        let dir = init_repo();
        let previous_main = crate::gitrepo::rev_parse(dir.path(), "main").unwrap();
        let next = author_commit_for_reconcile(dir.path(), &previous_main, "feature.txt");
        let (_origin, remote) = push_main_to_a_fresh_origin(dir.path());
        let (state, auth_id) = state_with_bare_authorization(&previous_main, &next, &next);
        let d = reconciled_data(&auth_id, &previous_main, &next, &next);
        let err = verify_review_merge_reconciled(dir.path(), &remote, &state, &d).unwrap_err();
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
        let (_origin, remote) = push_main_to_a_fresh_origin(dir.path());
        let (state, auth_id) = state_with_bare_authorization(&previous_main, &next, &next);
        let d = reconciled_data(&auth_id, &previous_main, &next, &next);
        verify_review_merge_reconciled(dir.path(), &remote, &state, &d).expect("must accept");
    }

    /// The exact scenario `verify_review_merge_reconciled`'s doc comment
    /// describes: `main` genuinely advanced on the shared remote, but *this*
    /// checkout's own local `refs/heads/main` never moved (as it wouldn't,
    /// for a bootstrap coordinator recovering after a different reviewer's
    /// host pushed and went offline). Before this fix this hard-rejected
    /// with "not a first-parent successor" purely because of stale local
    /// state -- a real bug in the exact recovery path AGENT_REVIEW.md
    /// section 11 describes.
    #[test]
    fn verify_review_merge_reconciled_accepts_when_only_the_remotes_main_advanced() {
        let dir = init_repo();
        let previous_main = crate::gitrepo::rev_parse(dir.path(), "main").unwrap();
        let (_origin, remote) = push_main_to_a_fresh_origin(dir.path());
        // `next` is built and pushed directly to the remote, bypassing this
        // checkout's own `refs/heads/main` entirely -- mirroring a *different*
        // host having pushed the merge.
        let origin_wt = tempfile::tempdir().unwrap();
        git(origin_wt.path(), &["clone", "--quiet", &remote, "."]);
        git(origin_wt.path(), &["config", "user.email", "t@e.com"]);
        git(origin_wt.path(), &["config", "user.name", "T"]);
        std::fs::write(origin_wt.path().join("feature.txt"), "x").unwrap();
        git(origin_wt.path(), &["add", "feature.txt"]);
        git(
            origin_wt.path(),
            &["commit", "-q", "-m", "add feature\n\nAgent-Bus-Agent: zoe"],
        );
        let next = crate::gitrepo::rev_parse(origin_wt.path(), "HEAD").unwrap();
        let push = crate::gitrepo::run(origin_wt.path(), &["push", &remote, "main"]).unwrap();
        assert!(push.success, "{push:?}");
        assert_eq!(
            crate::gitrepo::rev_parse(dir.path(), "refs/heads/main").unwrap(),
            previous_main,
            "this checkout's own local main must genuinely never have moved"
        );

        let (state, auth_id) = state_with_bare_authorization(&previous_main, &next, &next);
        let d = reconciled_data(&auth_id, &previous_main, &next, &next);
        verify_review_merge_reconciled(dir.path(), &remote, &state, &d).expect(
            "must accept a merge only visible on the remote, not this checkout's stale local main",
        );
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
        // No real remote exists at "origin" -- proving this path never
        // reaches the fetch at all, since a fetch failure would itself be a
        // hard `Err`, not the `Ok(())` this test expects.
        verify_review_merge_reconciled(dir.path(), "origin", &state, &d)
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
        verify_review_merge_reconciled(dir.path(), "origin", &state, &d)
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
            merge_engine_version: short(FOREIGN_ENGINE_VERSION),
            design_commit: ObjectId::parse("0".repeat(40)).unwrap(),
            helper_commit: ObjectId::parse("0".repeat(40)).unwrap(),
        };
        crate::outbox::submit(
            f.repo.path(),
            "activate",
            &Candidate::new(&f.coord1, &EventData::MergeEngineActivated(data), vec![]),
        )
        .unwrap();
        // Must actually reach `f.remote`, not just commit locally: this
        // fixture's other identities (`f.reviewer`, below) share this exact
        // repo, and their own later gate-17 syncs fetch coord1's stream FROM
        // the remote -- a merely-local-only commit here leaves coord1's
        // local ref ahead of the remote's, which a later fetch then rejects
        // as non-fast-forward (`drain_outbox` alone never pushes; only
        // `drain_and_publish` does).
        let (drained, _receipt) = drain_and_publish(
            f.repo.path(),
            f.repo.path(),
            &f.coord1,
            &short("host1"),
            0,
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
            &f.remote,
        )
        .unwrap()
    }

    #[test]
    fn drain_outbox_rejects_review_merge_reconciled_when_main_was_never_advanced() {
        let f = build_review_fixture(Some("zoe"));
        let (candidate, authorization_id) = authorized_and_published(&f);
        // `main` deliberately left at `previous_main` -- the candidate was
        // never actually pushed. Still needs to exist on `f.remote` at all
        // (unadvanced) for `verify_review_merge_reconciled`'s own fetch to
        // succeed, so this test exercises the real "not a first-parent
        // successor" rejection rather than an unrelated fetch failure.
        let push =
            crate::gitrepo::run(f.repo.path(), &["push", &f.remote, "refs/heads/main"]).unwrap();
        assert!(push.success, "{push:?}");
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
        // `verify_review_merge_reconciled` fetches `main` from `f.remote`,
        // not this checkout's own local ref (round-6 review) -- so the
        // advance must actually reach the remote to be visible at all.
        let push =
            crate::gitrepo::run(f.repo.path(), &["push", &f.remote, "refs/heads/main"]).unwrap();
        assert!(push.success, "{push:?}");

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

    // --------------------------------------------- gate 12, audience exactness

    /// Builds a state with `members` active in one epoch, each subscribed to
    /// the topics named for them.
    fn state_with_subscribers(
        members: &[(&str, Role, &[&str])],
    ) -> (crate::state::BusState, crate::registry::RosterEpoch) {
        let mut active = std::collections::BTreeMap::new();
        for (name, role, _) in members {
            active.insert(
                a(name),
                crate::registry::MemberBinding {
                    role: *role,
                    host: short("host1"),
                    coordinator_custody_epoch: 0,
                    standby: None,
                },
            );
        }
        let epoch =
            crate::registry::RosterEpoch::root(ObjectId::parse("0".repeat(40)).unwrap(), active);
        let mut state = crate::state::BusState::new(crate::bootstrap::BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: ObjectId::parse("1".repeat(40)).unwrap(),
            merge_engine: crate::bootstrap::SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: FOREIGN_ENGINE_VERSION.to_string(),
        });
        state.known_epochs.insert(epoch.id.clone(), epoch.clone());
        state.roster_epoch = Some(epoch.clone());
        for (name, role, topics) in members {
            let agent = a(name);
            state.agents.insert(
                agent.clone(),
                crate::state::AgentState {
                    agent: agent.clone(),
                    display_name: short(name),
                    primary_role: *role,
                    purpose: text("p"),
                    provider: None,
                    model: None,
                    status: LifecycleStatus::Active,
                    status_note: text(""),
                    product_branch: None,
                    product_commit: None,
                    last_lifecycle_event: EventId::new(&agent, 0),
                    retired: false,
                    scope: None,
                    plan: None,
                    progress_tail: vec![],
                    next_seq: 1,
                    subscribed_topics: crate::scalars::StringSet::from_iter(topics.iter().map(
                        |t| crate::scalars::CoordinationTopic::parse((*t).to_string()).unwrap(),
                    )),
                },
            );
        }
        (state, epoch)
    }

    fn broadcast_to_subscribers(
        epoch: &crate::registry::RosterEpoch,
        snapshot: &[&str],
    ) -> crate::events::BroadcastPublished {
        crate::events::BroadcastPublished {
            topics: crate::scalars::StringSet::from_iter([
                crate::scalars::CoordinationTopic::parse("release.main".into()).unwrap(),
            ]),
            importance: crate::common::Importance::Informational,
            summary: short("s"),
            detail: text("d"),
            affected_paths: crate::scalars::StringSet::default(),
            affected_interfaces: crate::scalars::StringSet::default(),
            product_commits: crate::scalars::StringSet::default(),
            audience_selector: crate::common::AudienceSelector::TopicSubscribers(
                crate::scalars::CoordinationTopic::parse("release.main".into()).unwrap(),
            ),
            audience_epoch: epoch.id.clone(),
            audience_snapshot: crate::scalars::StringSet::from_iter(snapshot.iter().map(|n| a(n))),
            acknowledgement: crate::common::AckRequirement::None,
            deadline: None,
            supersedes: crate::scalars::StringSet::default(),
            workaround: None,
            expiry_condition: None,
        }
    }

    /// Gate 12 ("audience resolution is exact") lives here, not in `apply`.
    ///
    /// `apply_broadcast_published` deliberately does not check it: the state
    /// a selector resolves against is mutable and unpinned, and reduction
    /// orders events by `refs` rather than by `observed`, so the deciding
    /// `subscription.set` is routinely applied after the broadcast. Asking
    /// there wedged honest publishers. Here `state` is the publishing host's
    /// own fully-reduced view, so the question has one answer.
    #[test]
    fn verify_broadcast_published_enforces_audience_exactness() {
        let (state, epoch) = state_with_subscribers(&[
            ("alice", Role::Implementor, &[]),
            ("bob", Role::Implementor, &["release.main"]),
            ("carol", Role::Implementor, &["release.main"]),
        ]);

        verify_broadcast_published(&state, &broadcast_to_subscribers(&epoch, &["bob", "carol"]))
            .expect("the exact resolved audience is accepted");

        let err = verify_broadcast_published(&state, &broadcast_to_subscribers(&epoch, &["bob"]))
            .expect_err("a snapshot omitting a subscriber is refused");
        assert!(
            err.to_string().contains("missing [\"carol\"]"),
            "the message must name who was dropped: {err}"
        );

        let err = verify_broadcast_published(
            &state,
            &broadcast_to_subscribers(&epoch, &["bob", "carol", "alice"]),
        )
        .expect_err("a snapshot naming a non-subscriber is refused");
        assert!(
            err.to_string().contains("unexpected [\"alice\"]"),
            "the message must name who was invented: {err}"
        );
    }

    /// An unknown epoch is left to `apply::dry_run`, which reports it with a
    /// clearer message moments later -- this gate must not duplicate it.
    #[test]
    fn verify_broadcast_published_defers_an_unknown_epoch() {
        let (mut state, epoch) =
            state_with_subscribers(&[("alice", Role::Implementor, &["release.main"])]);
        state.known_epochs.clear();
        verify_broadcast_published(&state, &broadcast_to_subscribers(&epoch, &["nobody-here"]))
            .expect("an unknown epoch is deferred, not judged");
    }

    // ------------------------------------- contested-predecessor publication gate

    /// The other half of `apply::building_on_a_contested_predecessor_still_
    /// reduces`: reduction records such an event, publication refuses it.
    ///
    /// Reduction cannot ask the question -- `is_contested` reads group
    /// membership that grows as concurrent candidates reduce, and nothing
    /// the event carries references the candidate that contests its
    /// predecessor, so the answer depended on fetch order. Here `state` is
    /// the publishing host's own fully-reduced view and there is one answer.
    ///
    /// Covers every kind the gate dispatches on, because the mapping from
    /// event to predecessor field is exactly where a future kind gets
    /// forgotten, and a forgotten kind fails open.
    #[test]
    fn the_publication_gate_refuses_a_contested_predecessor() {
        use crate::events::{
            DependencyReassigned, DependencyRejected, DependencyResolved, HandoffAccepted,
            HandoffDeclined, HandoffWithdrawn, IssueReassigned, IssueRejected, IssueResolved,
        };

        let contested = EventId::new(&a("alice"), 3);
        let quiet = EventId::new(&a("alice"), 9);

        // A state in which `contested` is a member of a live two-candidate
        // race, and `quiet` is not.
        let mut state = crate::state::BusState::new(crate::bootstrap::BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: ObjectId::parse("1".repeat(40)).unwrap(),
            merge_engine: crate::bootstrap::SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: FOREIGN_ENGINE_VERSION.to_string(),
        });
        state
            .exclusive
            .record("issue:race", &contested)
            .expect("first candidate");
        state
            .exclusive
            .record("issue:race", &EventId::new(&a("bob"), 4))
            .expect("second, concurrent candidate");
        assert!(state.exclusive.is_contested(&contested));

        let text = |t: &str| Text::parse(t.to_string()).unwrap();
        let with = |p: &EventId| -> Vec<EventData> {
            vec![
                EventData::IssueResolved(IssueResolved {
                    issue: p.clone(),
                    assignment: p.clone(),
                    summary: text("s"),
                    fix_commit: None,
                    verification: vec![],
                }),
                EventData::IssueRejected(IssueRejected {
                    issue: p.clone(),
                    assignment: p.clone(),
                    reason: text("r"),
                    normative_refs: vec![],
                }),
                EventData::IssueReassigned(IssueReassigned {
                    issue: p.clone(),
                    previous_assignment: p.clone(),
                    previous_target: a("bob"),
                    new_target: a("carol"),
                    reason: text("r"),
                }),
                EventData::DependencyResolved(DependencyResolved {
                    dependency: p.clone(),
                    assignment: p.clone(),
                    summary: text("s"),
                    product_commit: None,
                    verification: vec![],
                }),
                EventData::DependencyRejected(DependencyRejected {
                    dependency: p.clone(),
                    assignment: p.clone(),
                    reason: text("r"),
                }),
                EventData::DependencyReassigned(DependencyReassigned {
                    dependency: p.clone(),
                    previous_assignment: p.clone(),
                    previous_target: a("bob"),
                    new_target: a("carol"),
                    reason: text("r"),
                }),
                EventData::HandoffAccepted(HandoffAccepted {
                    handoff: p.clone(),
                    note: text(""),
                }),
                EventData::HandoffDeclined(HandoffDeclined {
                    handoff: p.clone(),
                    reason: text("r"),
                }),
                EventData::HandoffWithdrawn(HandoffWithdrawn {
                    handoff: p.clone(),
                    reason: text("r"),
                }),
            ]
        };

        for data in with(&contested) {
            let err = verify_predecessor_not_contested(&state, &data)
                .expect_err("a contested predecessor must not publish");
            assert!(
                err.to_string()
                    .contains("is itself part of an unresolved lifecycle conflict"),
                "{}: {err}",
                data.kind()
            );
        }
        for data in with(&quiet) {
            verify_predecessor_not_contested(&state, &data).unwrap_or_else(|e| {
                panic!(
                    "an uncontested predecessor must publish ({}): {e}",
                    data.kind()
                )
            });
        }
    }

    /// The other half of `apply::a_reviewer_retiring_concurrently_with_a_
    /// nomination_still_reduces`: reduction records it, publication refuses
    /// it.
    #[test]
    fn the_publication_gate_refuses_an_inactive_participant() {
        let (mut state, _epoch) = state_with_subscribers(&[
            ("alice", Role::Implementor, &[]),
            ("bob", Role::Reviewer, &[]),
        ]);
        let nomination = |reviewer: &str| {
            EventData::ReviewNominated(crate::events::ReviewRequest {
                authors: crate::scalars::StringSet::from_iter([a("alice")]),
                product_branch: crate::scalars::Branch::parse("refs/heads/agent/alice/x".into())
                    .unwrap(),
                reviewer: a(reviewer),
                required_checks: vec![],
                review_scope: crate::scalars::StringSet::from_iter([
                    crate::scalars::PathClaim::parse("Grass/**".into()).unwrap(),
                ]),
                summary: text("s"),
                target_branch: crate::scalars::Branch::parse("refs/heads/main".into()).unwrap(),
                evidence: crate::scalars::StringSet::default(),
            })
        };
        let data = nomination("bob");

        verify_participants_active(&state, &data).expect("an active reviewer publishes normally");

        state.agents.get_mut(&a("bob")).unwrap().retired = true;
        let err = verify_participants_active(&state, &data)
            .expect_err("a retired reviewer must not be handed a review");
        assert!(
            err.to_string().contains("retired or otherwise inactive"),
            "{err}"
        );

        // An agent nobody registered is a different failure, and says so.
        let unknown = nomination("nobody");
        let err = verify_participants_active(&state, &unknown).expect_err("unknown agent");
        assert!(err.to_string().contains("not a registered agent"), "{err}");
    }

    /// The `retired` half of author liveness, in its new home.
    ///
    /// `require_self_active_role` deliberately does not read `retired`:
    /// `apply_retired` requires a coordinator and forbids retiring yourself,
    /// so the flag always arrives on somebody else's stream and reading it
    /// during replay made a retired agent's own published history unreducible
    /// (`apply::an_agent_retired_by_a_coordinator_can_still_have_its_own_history_reduced`).
    ///
    /// The rule is not dropped, it is asked here. Covering all four kinds
    /// whose handlers gave it up, plus one that never asked it, because the
    /// kind list is exactly where an addition gets forgotten and a forgotten
    /// kind fails open.
    #[test]
    fn the_publication_gate_refuses_a_retired_author() {
        let (mut state, _epoch) = state_with_subscribers(&[
            ("alice", Role::Implementor, &[]),
            ("aud", Role::Auditor, &[]),
        ]);

        let scope_set = EventData::ScopeSet(crate::events::ScopeSet {
            base_code_commit: ObjectId::parse("2".repeat(40)).unwrap(),
            exclusive: crate::scalars::StringSet::from_iter([crate::scalars::PathClaim::parse(
                "Grass/**".into(),
            )
            .unwrap()]),
            shared: crate::scalars::StringSet::default(),
            exports: crate::scalars::StringSet::default(),
            depends_on: vec![],
            note: text("n"),
        });

        // Active: publishes.
        verify_author_active(&state, &a("alice"), &scope_set)
            .expect("an active author publishes normally");

        state.agents.get_mut(&a("alice")).unwrap().retired = true;
        let err = verify_author_active(&state, &a("alice"), &scope_set)
            .expect_err("a retired author must not publish a scope claim");
        assert!(
            err.to_string().contains("retired or otherwise inactive"),
            "{err}"
        );

        // A kind the gate deliberately does not cover is unaffected, so the
        // list is doing real work rather than matching everything.
        let status = EventData::AgentStatus(crate::events::AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: text("back"),
            product_branch: None,
            product_commit: None,
        });
        verify_author_active(&state, &a("alice"), &status).expect(
            "agent.status is how a retired identity would be resumed; it must not be gated here",
        );
    }
}
