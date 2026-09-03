//! Read-side: turning fetched (or already-local) registry/stream refs into
//! a `BusState` snapshot, carrying the freshness class every query result
//! must state (docs/AGENT_COORDINATION_EVOLUTION.md section 2.4: "Every
//! human and machine-readable result states its snapshot receipt, roster
//! epoch, causal frontier, last successful synchronization time, and
//! freshness class").
//!
//! There is deliberately no persistent "subscription policy" or incremental
//! index here yet -- every call re-reads every active member's full stream.
//! That upper bound is `reduce`'s own documented cost ("cold validation:
//! linear in all retained events, parallel by stream"); incremental sync
//! (fetching and re-reducing only advanced streams) is real further work,
//! not silently assumed done.

use crate::error::{invalid, AbError, AbResult};
use crate::registry::RosterEpoch;
use crate::scalars::{Agent, ObjectId, Timestamp};
use crate::state::BusState;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Whether a [`Snapshot`] reflects a just-completed remote probe or only
/// whatever was already known locally. Currency-sensitive operations (merge
/// readiness, reassignment, schema activation, all-active audience
/// construction) must refuse a `Cached` snapshot and require a synced one
/// instead, rather than silently act on a stale cut -- this type exists so
/// that refusal is a compile-time-visible match arm, not a convention a
/// caller can forget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Freshness {
    Cached,
    CurrentAsOfRemoteProbe,
}

/// One reduced view of the bus: the resulting `BusState`, the exact roster
/// epoch it was built against, each contributing stream's tip (the
/// snapshot's own receipt -- what a later validation re-checks itself
/// against, not merely diagnostic), how fresh it is, and when this local
/// checkout last completed a successful remote synchronization (`None` if
/// never -- see [`read_last_synced`]). Every field here, together with
/// `freshness`, is what section 2.4 requires every result to state
/// ("snapshot receipt, roster epoch, causal frontier, last successful
/// synchronization time, and freshness class"); `last_synced` in particular
/// is diagnostic only -- "time since sync ... never confers authority", so
/// nothing here treats a recent `last_synced` as a substitute for an actual
/// `CurrentAsOfRemoteProbe` freshness class.
#[derive(Debug, Clone)]
pub struct Snapshot {
    pub state: BusState,
    pub roster_epoch: RosterEpoch,
    pub stream_tips: BTreeMap<Agent, ObjectId>,
    pub freshness: Freshness,
    pub last_synced: Option<Timestamp>,
}

/// Reduces whatever is already local -- no network round trip -- into a
/// `Snapshot` marked `Cached`. Fails if the registry has never been created
/// locally at all. `last_synced` reports whatever [`synced_snapshot`] most
/// recently recorded on this local checkout (via `git_common_dir`), or
/// `None` if a synchronization has never yet succeeded here -- never a
/// fabricated or `now()`-derived value, since a cached read must be able to
/// report a last-sync time from long before "now".
pub fn cached_snapshot(
    repo: &Path,
    git_common_dir: &Path,
    worktrees_dir: &Path,
) -> AbResult<Snapshot> {
    let last_synced = read_last_synced(git_common_dir)?;
    let mut snapshot = reduce_local(repo, worktrees_dir, Freshness::Cached)?;
    snapshot.last_synced = last_synced;
    Ok(snapshot)
}

/// Fetches the registry ref, then every currently active member's stream
/// ref, from `remote` into their ordinary local branch refs (a plain,
/// non-force fetch -- see `gitrepo::fetch_refspecs`'s own doc for why that
/// alone is enough to reject an unexpected remote history rewrite), and
/// reduces the result into a `Snapshot` marked `CurrentAsOfRemoteProbe`.
/// The registry must be fetched first: it is what decides which stream
/// refs to fetch next.
///
/// Once the fetch itself succeeds, the current time is durably recorded
/// (via `git_common_dir`, see [`record_last_synced`]) as this checkout's
/// last successful synchronization time *before* the subsequent local
/// reduction is attempted -- "synchronization" here means the remote probe
/// itself succeeded, which is true independent of whether reducing what was
/// just fetched later fails for some unrelated reason (e.g. a malformed
/// event). A later `cached_snapshot` (or a `synced_snapshot` whose own
/// fetch fails) then correctly reports that recorded time rather than
/// `None`.
pub fn synced_snapshot(
    repo: &Path,
    git_common_dir: &Path,
    remote: &str,
    worktrees_dir: &Path,
) -> AbResult<Snapshot> {
    // Existence checked first, same reasoning as the stream refs below: a
    // bus that has never been bootstrapped on `remote` yet is an ordinary,
    // expected state (not a fetch failure) and deserves this function's own
    // clear message, not `fetch_refspecs_ok`'s generic "couldn't find remote
    // ref" -- while a remote that genuinely cannot be reached at all must
    // still hard-fail here, via `remote_refs_existing`'s own `ls-remote`
    // check, rather than silently falling through to reduce stale local
    // state (round-6 adversarial review).
    let registry_ref = crate::registry::REGISTRY_REF.to_string();
    let registry_exists =
        crate::gitrepo::remote_refs_existing(repo, remote, std::slice::from_ref(&registry_ref))?
            .contains(&registry_ref);
    if !registry_exists {
        return Err(invalid("no registry root exists on the remote"));
    }
    crate::gitrepo::fetch_refspecs_ok(repo, remote, &[format!("{registry_ref}:{registry_ref}")])?;

    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists on the remote"))?;
    let epoch =
        crate::registry::read_epoch(repo, &registry_tip, &worktrees_dir.join("_sync_epoch"))?;

    // A member registered in this epoch may not have published its own
    // stream root yet (reduce_local's own comment: "a real, expected
    // state"). A single unresolvable refspec fails a multi-ref `git fetch`
    // in its entirety -- nothing gets fetched, not even the members that DO
    // have a stream -- so existence is checked first and only refs that
    // actually exist remotely are fetched.
    let candidate_refnames: Vec<String> = epoch
        .active_members
        .keys()
        .map(|agent| crate::stream::stream_ref(agent).into_string())
        .collect();
    let existing = crate::gitrepo::remote_refs_existing(repo, remote, &candidate_refnames)?;
    let stream_refspecs: Vec<String> = candidate_refnames
        .iter()
        .filter(|r| existing.contains(*r))
        .map(|r| format!("{r}:{r}"))
        .collect();
    if !stream_refspecs.is_empty() {
        crate::gitrepo::fetch_refspecs_ok(repo, remote, &stream_refspecs)?;
    }

    let now = Timestamp::now_utc();
    record_last_synced(git_common_dir, &now)?;

    let mut snapshot = reduce_local(repo, worktrees_dir, Freshness::CurrentAsOfRemoteProbe)?;
    snapshot.last_synced = Some(now);
    Ok(snapshot)
}

/// The durable record of this local checkout's last successful
/// synchronization time, kept under the same `<git_common_dir>/agent-bus/`
/// operational-state directory `outbox.rs`'s outbox and the CLI's read
/// worktrees already use -- not part of any committed tree (git history
/// stays substrate for bus events only), and not derived from `SystemTime::
/// now()` at read time.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct LastSyncedRecord {
    last_synced: Timestamp,
}

fn last_synced_path(git_common_dir: &Path) -> PathBuf {
    git_common_dir.join("agent-bus").join("last_synced.json")
}

/// Reads this local checkout's last successful synchronization time, or
/// `None` if [`synced_snapshot`] has never yet completed a fetch here.
pub fn read_last_synced(git_common_dir: &Path) -> AbResult<Option<Timestamp>> {
    let path = last_synced_path(git_common_dir);
    match std::fs::read(&path) {
        Ok(bytes) => {
            let record: LastSyncedRecord = serde_json::from_slice(&bytes)?;
            Ok(Some(record.last_synced))
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(AbError::Io {
            path: path.display().to_string(),
            source: e,
        }),
    }
}

fn record_last_synced(git_common_dir: &Path, at: &Timestamp) -> AbResult<()> {
    let path = last_synced_path(git_common_dir);
    let dir = path.parent().expect("last_synced_path always has a parent");
    std::fs::create_dir_all(dir).map_err(|e| AbError::Io {
        path: dir.display().to_string(),
        source: e,
    })?;
    let record = LastSyncedRecord {
        last_synced: at.clone(),
    };
    crate::storage::atomic_write(&path, &serde_json::to_vec_pretty(&record)?)
}

fn reduce_local(repo: &Path, worktrees_dir: &Path, freshness: Freshness) -> AbResult<Snapshot> {
    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists locally"))?;
    let epoch =
        crate::registry::read_epoch(repo, &registry_tip, &worktrees_dir.join("_reduce_epoch"))?;
    // Every epoch reachable from the tip, not just the current one -- a
    // complete frontier authored against an older epoch must remain
    // re-validatable forever (gate 5), and `apply::require_complete_
    // frontier`/`apply_broadcast_published` look the *named* epoch up here
    // rather than trusting whatever is current at reduction time.
    let known_epochs = crate::registry::read_epoch_chain(
        repo,
        &registry_tip,
        &worktrees_dir.join("_reduce_epoch_chain"),
    )?;
    let config = crate::registry::read_bus_config(
        repo,
        &registry_tip,
        &worktrees_dir.join("_reduce_config"),
    )?;

    let mut streams = BTreeMap::new();
    let mut stream_tips = BTreeMap::new();
    for agent in epoch.active_members.keys() {
        let tip = match crate::stream::read_stream_tip(repo, agent)? {
            Some(tip) => tip,
            // Registered in this epoch but has not yet published its own
            // stream root -- a real, expected state, not an error: the
            // registry transition that added the member and that member's
            // first `agent.registered` event are two separate publications.
            None => continue,
        };
        let reads_dir = worktrees_dir.join(format!("_reduce_stream_{agent}"));
        let (_header, log) = crate::stream::read_stream(repo, agent, &reads_dir)?;
        streams.insert(agent.clone(), log);
        stream_tips.insert(agent.clone(), tip);
    }

    let state = crate::apply::reduce(config, Some(epoch.clone()), known_epochs, &streams)?;
    Ok(Snapshot {
        state,
        roster_epoch: epoch,
        stream_tips,
        freshness,
        // Filled in by the two public callers above, which each know the
        // correct value in their own way; `reduce_local` itself has no
        // opinion on it.
        last_synced: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{AgentStatusEvent, EventData, LifecycleStatus, Role};
    use crate::outbox::Candidate;
    use crate::scalars::{Agent, Short, Text};

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> Text {
        Text::parse(s.to_string()).unwrap()
    }

    fn git(dir: &Path, args: &[&str]) {
        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?} failed in {}", dir.display());
    }

    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        git(path, &["init", "--quiet", "-b", "main"]);
        git(path, &["config", "user.email", "test@example.com"]);
        git(path, &["config", "user.name", "Test"]);
        std::fs::write(path.join("README.md"), "hello\n").unwrap();
        git(path, &["add", "README.md"]);
        git(path, &["commit", "-q", "-m", "initial"]);
        dir
    }

    fn init_bare_origin() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        git(dir.path(), &["init", "--quiet", "--bare", "-b", "main"]);
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

    /// `read_last_synced`'s generic `AbError::Io` arm, distinct from the
    /// "never synced yet" `NotFound` case: `last_synced.json` exists as a
    /// directory here, not a file, so `fs::read` on it fails with a real
    /// I/O error that is not `NotFound` (a plain missing *parent*
    /// component, tried first, is reported as `NotFound` on this platform
    /// and would not exercise this arm -- a directory in the file's own
    /// place is what reliably does).
    #[test]
    fn read_last_synced_reports_a_genuine_io_error_not_just_never_synced() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(dir.path().join("agent-bus").join("last_synced.json")).unwrap();
        let err = read_last_synced(dir.path()).unwrap_err();
        assert!(matches!(err, crate::error::AbError::Io { .. }), "{err}");
    }

    /// `synced_snapshot` surfaces a genuine I/O error from `record_last_
    /// synced` (called only after the fetch itself has already succeeded)
    /// rather than silently losing it: blocking `agent-bus` the same way as
    /// above makes `record_last_synced`'s own `create_dir_all` fail.
    #[test]
    fn synced_snapshot_reports_io_error_when_last_synced_cannot_be_recorded() {
        let origin = init_bare_origin();

        let host_a = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(host_a.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            host_a.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            crate::scalars::ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &host_a.path().join("_genesis_wt"),
        )
        .unwrap();
        let registry_tip = crate::registry::read_registry_tip(host_a.path())
            .unwrap()
            .unwrap();
        crate::publish::publish(
            host_a.path(),
            &origin.path().to_string_lossy(),
            &[crate::publish::RefUpdate::new(
                crate::registry::REGISTRY_REF,
                registry_tip,
            )],
        )
        .unwrap();

        let host_b = init_repo();
        std::fs::write(host_b.path().join("agent-bus"), b"blocked").unwrap();
        let err = synced_snapshot(
            host_b.path(),
            host_b.path(),
            &origin.path().to_string_lossy(),
            &host_b.path().join("_sync_wt"),
        )
        .unwrap_err();
        assert!(matches!(err, crate::error::AbError::Io { .. }), "{err}");
        // The fetch itself genuinely succeeded before the recording step
        // failed, so nothing here should be mistaken for "no registry".
        assert!(!err.to_string().contains("no registry root"), "{err}");
    }

    #[test]
    fn cached_snapshot_fails_before_any_registry_exists() {
        let repo = init_repo();
        let err = cached_snapshot(repo.path(), repo.path(), &repo.path().join("_wt")).unwrap_err();
        assert!(err.to_string().contains("no registry root"), "{err}");
    }

    #[test]
    fn cached_snapshot_reduces_the_genesis_registration_alone() {
        let repo = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            crate::scalars::ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &repo.path().join("_genesis_wt"),
        )
        .unwrap();

        let snap =
            cached_snapshot(repo.path(), repo.path(), &repo.path().join("_snap_wt")).unwrap();
        assert_eq!(snap.freshness, Freshness::Cached);
        assert!(snap.roster_epoch.is_active_member(&coord1));
        assert!(snap.state.agents.contains_key(&coord1));
        assert_eq!(snap.stream_tips.len(), 1);
        // Nothing has ever synced in this repo -- a cached read before the
        // first successful remote probe must report `None`, not a
        // fabricated time.
        assert!(snap.last_synced.is_none());
    }

    /// Two hosts sharing one remote: host A publishes coord1's status event
    /// and pushes it; host B (a separate local clone/checkout of the same
    /// origin, never having run drain_outbox itself) must be able to pull
    /// coord1's stream via `synced_snapshot` alone and reduce the same
    /// state, purely from the remote.
    #[test]
    fn synced_snapshot_pulls_another_hosts_published_stream() {
        let origin = init_bare_origin();

        let host_a = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(host_a.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            host_a.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            crate::scalars::ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &host_a.path().join("_genesis_wt"),
        )
        .unwrap();
        crate::outbox::submit(
            host_a.path(),
            "client-1",
            &status_candidate(&coord1, "hello"),
        )
        .unwrap();
        crate::coordinator::drain_and_publish(
            host_a.path(),
            host_a.path(),
            &coord1,
            &short("host1"),
            0,
            &host_a.path().join("_wt"),
            &origin.path().to_string_lossy(),
        )
        .unwrap();
        // The registry root itself must also reach the remote for a fresh
        // host to bootstrap from -- drain_and_publish only pushes the
        // stream ref, so publish the registry ref directly here.
        let registry_tip = crate::registry::read_registry_tip(host_a.path())
            .unwrap()
            .unwrap();
        crate::publish::publish(
            host_a.path(),
            &origin.path().to_string_lossy(),
            &[crate::publish::RefUpdate::new(
                crate::registry::REGISTRY_REF,
                registry_tip,
            )],
        )
        .unwrap();

        let host_b = init_repo();
        // No synchronization has ever happened on host_b yet.
        assert!(read_last_synced(host_b.path()).unwrap().is_none());
        let snap = synced_snapshot(
            host_b.path(),
            host_b.path(),
            &origin.path().to_string_lossy(),
            &host_b.path().join("_sync_wt"),
        )
        .unwrap();
        assert_eq!(snap.freshness, Freshness::CurrentAsOfRemoteProbe);
        assert!(snap.roster_epoch.is_active_member(&coord1));
        let agent_state = snap.state.agents.get(&coord1).unwrap();
        assert_eq!(agent_state.next_seq, 2); // registration + the one status event
                                             // A successful sync leaves a real, non-fabricated `last_synced`,
                                             // both on the returned snapshot and durably on disk for a later
                                             // `cached_snapshot` to read back.
        let recorded = snap.last_synced.clone().expect("just synced successfully");
        assert_eq!(read_last_synced(host_b.path()).unwrap(), Some(recorded));
    }

    /// Regression: a registry epoch member who has not yet published their
    /// own stream root (a real, expected state -- see `reduce_local`'s own
    /// comment) used to break `synced_snapshot` *entirely*: `git fetch`
    /// fails a multi-refspec batch in full when even one refspec can't be
    /// resolved, so before `remote_refs_existing` filtering was added, a
    /// single not-yet-published member meant nothing was fetched at all,
    /// not even other members' streams that genuinely exist remotely.
    #[test]
    fn synced_snapshot_tolerates_a_registered_member_with_no_published_stream_yet() {
        let origin = init_bare_origin();

        let host_a = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(host_a.path(), "HEAD").unwrap();
        let (_config, epoch, _commit) = crate::bootstrap::genesis(
            host_a.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            crate::scalars::ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &host_a.path().join("_genesis_wt"),
        )
        .unwrap();
        crate::coordinator::drain_and_publish(
            host_a.path(),
            host_a.path(),
            &coord1,
            &short("host1"),
            0,
            &host_a.path().join("_wt"),
            &origin.path().to_string_lossy(),
        )
        .unwrap();

        // alice joins the roster epoch but never publishes her own stream
        // root -- registration and a member's first event are genuinely
        // two separate publications.
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
            host_a.path(),
            &epoch,
            members,
            &host_a.path().join("_transition_wt"),
        )
        .unwrap();
        crate::publish::publish(
            host_a.path(),
            &origin.path().to_string_lossy(),
            &[crate::publish::RefUpdate::new(
                crate::registry::REGISTRY_REF,
                new_epoch.id.clone(),
            )],
        )
        .unwrap();

        let host_b = init_repo();
        let snap = synced_snapshot(
            host_b.path(),
            host_b.path(),
            &origin.path().to_string_lossy(),
            &host_b.path().join("_sync_wt"),
        )
        .unwrap();
        assert!(snap.roster_epoch.is_active_member(&alice));
        assert!(snap.roster_epoch.is_active_member(&coord1));
        // coord1's real stream still reduced successfully...
        assert!(snap.state.agents.contains_key(&coord1));
        // ...while alice, registered but streamless, simply isn't in the
        // reduced agent map yet -- not an error, not a missing coord1 too.
        assert!(!snap.state.agents.contains_key(&alice));
    }

    #[test]
    fn synced_snapshot_fails_when_the_remote_has_no_registry_yet() {
        let origin = init_bare_origin();
        let repo = init_repo();
        let err = synced_snapshot(
            repo.path(),
            repo.path(),
            &origin.path().to_string_lossy(),
            &repo.path().join("_sync_wt"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("no registry root"), "{err}");
        // The fetch itself never got far enough to succeed (the registry
        // ref doesn't even exist on the remote), so nothing was recorded --
        // a failed synchronization must not fabricate a successful one.
        assert!(read_last_synced(repo.path()).unwrap().is_none());
    }

    /// Round-6 adversarial review: `fetch_refspecs` reports a rejected or
    /// failed `git fetch` via `success: false`, not an `Err` -- if
    /// `synced_snapshot` merely `?`-propagated it (as it used to), a genuine
    /// fetch failure would be silently swallowed, and this host's *stale*
    /// local state would be reduced and reported as `Freshness::
    /// CurrentAsOfRemoteProbe` with a freshly-recorded `last_synced`, exactly
    /// as if the probe had actually succeeded. Reproduced here: `host_b`
    /// syncs once successfully, `origin` then advances further, and a second
    /// sync attempt against an unreachable remote must hard-fail rather than
    /// silently re-report the now-stale first snapshot as current.
    #[test]
    fn synced_snapshot_fails_closed_when_the_fetch_itself_is_rejected_rather_than_reporting_stale_state_as_current(
    ) {
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();

        let host_a = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(host_a.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            host_a.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            crate::scalars::ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &host_a.path().join("_genesis_wt"),
        )
        .unwrap();
        let registry_tip = crate::registry::read_registry_tip(host_a.path())
            .unwrap()
            .unwrap();
        crate::publish::publish(
            host_a.path(),
            &remote,
            &[
                crate::publish::RefUpdate::new(crate::registry::REGISTRY_REF, registry_tip),
                crate::publish::RefUpdate::new(
                    crate::stream::stream_ref(&coord1).into_string(),
                    crate::stream::read_stream_tip(host_a.path(), &coord1)
                        .unwrap()
                        .unwrap(),
                ),
            ],
        )
        .unwrap();

        let host_b = init_repo();
        let first = synced_snapshot(
            host_b.path(),
            host_b.path(),
            &remote,
            &host_b.path().join("_wt1"),
        )
        .unwrap();
        assert_eq!(first.state.agents.get(&coord1).unwrap().next_seq, 1);
        let first_last_synced = first.last_synced.clone().unwrap();

        // `origin` genuinely advances further, unseen by `host_b` yet.
        crate::outbox::submit(
            host_a.path(),
            "client-1",
            &status_candidate(&coord1, "advanced"),
        )
        .unwrap();
        crate::coordinator::drain_and_publish(
            host_a.path(),
            host_a.path(),
            &coord1,
            &short("host1"),
            0,
            &host_a.path().join("_wt_advance"),
            &remote,
        )
        .unwrap();

        // A second sync attempt against a remote that cannot actually be
        // fetched from (not a genuine git repository at all) must hard-fail,
        // not silently re-report `host_b`'s now-stale first snapshot as
        // `CurrentAsOfRemoteProbe`.
        let bogus_remote = host_b.path().join("no-such-remote");
        let err = synced_snapshot(
            host_b.path(),
            host_b.path(),
            &bogus_remote.to_string_lossy(),
            &host_b.path().join("_wt2"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("failed"), "{err}");
        // The failed attempt must not fabricate a newer `last_synced` either.
        assert_eq!(
            read_last_synced(host_b.path()).unwrap(),
            Some(first_last_synced)
        );
    }

    /// If the fetch itself genuinely succeeds but the subsequent local
    /// reduction fails for an unrelated reason, the synchronization time is
    /// still recorded: "synchronization" means the remote probe succeeded,
    /// independent of whether interpreting what was fetched later fails.
    /// Simulated by publishing a registry root whose `epoch.json` is intact
    /// (so `synced_snapshot`'s own pre-record `read_epoch` call, and the
    /// fetch itself, both succeed) but whose `bus_config.json` is not valid
    /// JSON -- `reduce_local`'s `read_bus_config` call, which happens only
    /// *after* `synced_snapshot` has already recorded the sync time, is
    /// what actually fails.
    #[test]
    fn synced_snapshot_records_last_synced_even_when_the_subsequent_reduce_fails() {
        let origin = init_bare_origin();

        let host_a = init_repo();
        let coord1 = a("coord1");
        let review_from = crate::gitrepo::rev_parse(host_a.path(), "HEAD").unwrap();
        crate::bootstrap::genesis(
            host_a.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps"),
            "sha1".to_string(),
            crate::scalars::ObjectId::parse(review_from).unwrap(),
            short("host1"),
            &host_a.path().join("_genesis_wt"),
        )
        .unwrap();
        let registry_tip = crate::registry::read_registry_tip(host_a.path())
            .unwrap()
            .unwrap();

        // A second commit on the registry root, in an ordinary linked
        // worktree of host_a (so it shares host_a's own committer identity
        // config), that changes only `bus_config.json` -- `epoch.json`
        // carries forward from the parent tree untouched.
        let corrupt_dir = tempfile::tempdir().unwrap();
        let corrupt_path = corrupt_dir.path().to_str().unwrap().to_string();
        git(
            host_a.path(),
            &[
                "worktree",
                "add",
                "--detach",
                &corrupt_path,
                registry_tip.as_str(),
            ],
        );
        std::fs::write(
            corrupt_dir.path().join("bus_config.json"),
            "not valid json\n",
        )
        .unwrap();
        git(corrupt_dir.path(), &["add", "bus_config.json"]);
        git(
            corrupt_dir.path(),
            &["commit", "-q", "-m", "corrupt config"],
        );
        let corrupt_commit = crate::gitrepo::rev_parse(corrupt_dir.path(), "HEAD").unwrap();
        git(
            host_a.path(),
            &["worktree", "remove", "--force", &corrupt_path],
        );

        crate::publish::publish(
            host_a.path(),
            &origin.path().to_string_lossy(),
            &[crate::publish::RefUpdate::new(
                crate::registry::REGISTRY_REF,
                crate::scalars::ObjectId::parse(corrupt_commit).unwrap(),
            )],
        )
        .unwrap();

        let host_b = init_repo();
        let err = synced_snapshot(
            host_b.path(),
            host_b.path(),
            &origin.path().to_string_lossy(),
            &host_b.path().join("_sync_wt"),
        )
        .unwrap_err();
        // Confirms the failure is genuinely the intended one (the corrupt
        // config, reached only after a successful fetch and epoch read),
        // not some earlier failure this recipe didn't anticipate.
        assert!(err.to_string().contains("malformed bus config"), "{err}");

        // The fetch itself genuinely succeeded, so the synchronization time
        // was recorded despite the later reduce failure.
        assert!(read_last_synced(host_b.path()).unwrap().is_some());
    }
}
