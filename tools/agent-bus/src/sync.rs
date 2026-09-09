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
pub fn cached_snapshot(repo: &Path, git_common_dir: &Path) -> AbResult<Snapshot> {
    let last_synced = read_last_synced(git_common_dir)?;
    let mut snapshot = reduce_local(repo, Freshness::Cached)?;
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
pub fn synced_snapshot(repo: &Path, git_common_dir: &Path, remote: &str) -> AbResult<Snapshot> {
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

    // A member registered in this epoch may not have published its own
    // stream root yet (reduce_local's own comment: "a real, expected
    // state"). A single unresolvable refspec fails a multi-ref `git fetch`
    // in its entirety -- nothing gets fetched, not even the members that DO
    // have a stream -- so existence is checked first and only refs that
    // actually exist remotely are fetched.
    //
    // Fetched for every agent in *any* epoch of the chain, matching
    // `reduce_local` below. Fetching only the current roster would leave a
    // dropped member's stream absent locally, which is the same outage as
    // not loading it: the references into it stop resolving and reduction
    // fails on the first one.
    let known = crate::registry::read_epoch_chain(repo, &registry_tip)?;
    let all_members: std::collections::BTreeSet<crate::scalars::Agent> = known
        .values()
        .flat_map(|e| e.active_members.keys().cloned())
        .collect();
    let candidate_refnames: Vec<String> = all_members
        .iter()
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

    let mut snapshot = reduce_local(repo, Freshness::CurrentAsOfRemoteProbe)?;
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

fn reduce_local(repo: &Path, freshness: Freshness) -> AbResult<Snapshot> {
    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists locally"))?;
    // A full reduction reads the registry tip, its whole epoch lineage, the
    // bus config, and every active member's entire stream. Each of those was
    // a separate `git worktree add`/`remove` cycle before; one reader now
    // serves all of them straight from the object database.
    let reader = crate::gitobjects::Libgit2Reader::open(repo)?;
    let epoch = crate::registry::read_epoch_at(&reader, &registry_tip)?;
    // Every epoch reachable from the tip, not just the current one -- a
    // complete frontier authored against an older epoch must remain
    // re-validatable forever (gate 5), and `apply::require_complete_
    // frontier`/`apply_broadcast_published` look the *named* epoch up here
    // rather than trusting whatever is current at reduction time.
    let known_epochs = crate::registry::read_epoch_chain(repo, &registry_tip)?;
    let config = crate::registry::read_bus_config_at(&reader, &registry_tip)?;

    // Every agent named by *any* epoch in the chain, not just the current
    // one's active set -- the same argument the comment above makes for
    // epochs, which was never extended to the members inside them.
    //
    // A published stream is immutable and other agents' events reference it
    // by id forever. Loading only the current roster means that the moment a
    // roster transition drops a member, every `require_agent` naming them,
    // every `require_role` on them as a co-author or reviewer, and every
    // cross-stream `refs` lookup into their history stops resolving -- and
    // those are `Err` inside `apply::reduce`, which propagates on the first
    // one with no per-event isolation. An ordinary retirement would take the
    // whole bus down, on every host, permanently, because the log is
    // append-only and the references cannot be withdrawn.
    //
    // Latent rather than live today: `cli::register` is the only production
    // caller of `registry::propose_transition` and it only ever inserts. But
    // `propose_transition` takes an arbitrary member map, AGENT_BUS_SCHEMA.md
    // section 2.1 names retirement as an epoch transition, and a test in
    // `apply.rs` already constructs a removal. The set is a union over the
    // chain, so it is a pure function of the registry history and identical
    // on every host.
    let all_members: std::collections::BTreeSet<crate::scalars::Agent> = known_epochs
        .values()
        .flat_map(|e| e.active_members.keys().cloned())
        .collect();

    let mut streams = BTreeMap::new();
    let mut stream_tips = BTreeMap::new();
    for agent in &all_members {
        let tip = match crate::stream::read_stream_tip(repo, agent)? {
            Some(tip) => tip,
            // Registered in this epoch but has not yet published its own
            // stream root -- a real, expected state, not an error: the
            // registry transition that added the member and that member's
            // first `agent.registered` event are two separate publications.
            None => continue,
        };
        let (_header, log) = crate::stream::read_stream_at(&reader, &tip, agent)?;
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
        let err = cached_snapshot(repo.path(), repo.path()).unwrap_err();
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
        )
        .unwrap();

        let snap = cached_snapshot(repo.path(), repo.path()).unwrap();
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
        )
        .unwrap();
        crate::coordinator::drain_and_publish(
            host_a.path(),
            host_a.path(),
            &coord1,
            &short("host1"),
            0,
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
        let new_epoch =
            crate::registry::propose_transition(host_a.path(), &epoch, members).unwrap();
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
        let err = synced_snapshot(repo.path(), repo.path(), &origin.path().to_string_lossy())
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
    /// as if the probe had actually succeeded.
    ///
    /// Round-7 test-attacking review found this test's own `bogus_remote`
    /// (a nonexistent local path) actually failed at the *earlier*
    /// `remote_refs_existing` (`ls-remote`) existence check, never reaching
    /// either `fetch_refspecs_ok` call this test is meant to guard -- proven
    /// by mutation: reverting either call site back to plain `fetch_
    /// refspecs` (discarding `.success`, i.e. reinstating the exact
    /// pre-round-6 bug) still passed this test. Rewritten to force a
    /// *genuine* non-fast-forward rejection instead: the registry ref
    /// genuinely exists on `remote` (so the existence check passes and the
    /// first `fetch_refspecs_ok` call is actually reached), but `origin`
    /// force-rewrites it to a completely unrelated commit first -- an
    /// unexpected remote history rewrite, exactly what a non-force fetch
    /// must reject (AGENT_COORDINATION_EVOLUTION.md section 1: "force
    /// pushes... are prohibited").
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
        let first = synced_snapshot(host_b.path(), host_b.path(), &remote).unwrap();
        assert_eq!(first.state.agents.get(&coord1).unwrap().next_seq, 1);
        let first_last_synced = first.last_synced.clone().unwrap();

        // `origin`'s registry ref is force-rewritten to a completely
        // unrelated commit -- still genuinely present on `remote` (the
        // existence check must pass), but not a descendant of what `host_b`
        // already fetched, so a plain, non-force fetch must reject it.
        git(host_a.path(), &["checkout", "-q", "--orphan", "unrelated"]);
        git(host_a.path(), &["rm", "-rf", "-q", "."]);
        std::fs::write(host_a.path().join("unrelated.txt"), "x").unwrap();
        git(host_a.path(), &["add", "unrelated.txt"]);
        git(host_a.path(), &["commit", "-q", "-m", "unrelated root"]);
        let unrelated = crate::gitrepo::rev_parse(host_a.path(), "HEAD").unwrap();
        git(
            host_a.path(),
            &[
                "push",
                "--force",
                &remote,
                &format!("{unrelated}:{}", crate::registry::REGISTRY_REF),
            ],
        );

        // A second sync attempt must hard-fail on the genuinely rejected
        // fetch, not silently re-report `host_b`'s now-stale first snapshot
        // as `CurrentAsOfRemoteProbe`.
        let err = synced_snapshot(host_b.path(), host_b.path(), &remote).unwrap_err();
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

    // ---------------------------------------------------------- two hosts
    //
    // AGENT_COORDINATION_EVOLUTION.md section 2.1 ("An agent may move
    // between hosts without changing its stream identity; the registry
    // determines which host custody epoch may advance that ref"), section
    // 2.4's custody and succession rules, and gates 6/7/19.
    //
    // Everything below runs two *separate clones* of one bare origin on
    // purpose. Several of this crate's worst defects -- the merge
    // -authorization bootstrap deadlock, the `git branch -f` ref shadowing,
    // the `build_frontier` gate-4 gap -- were invisible to single
    // -repository tests, because one repository can never show a host
    // reasoning about facts it has not fetched, nor two custodians racing
    // for one stream ref.

    /// One bare origin plus two independent clones of it, standing in for
    /// two physical development hosts.
    struct Fleet {
        origin: tempfile::TempDir,
        host_a: tempfile::TempDir,
        host_b: tempfile::TempDir,
    }

    impl Fleet {
        fn remote(&self) -> String {
            self.origin.path().to_string_lossy().into_owned()
        }
    }

    /// Bootstraps `coord1` on `host_a` under host name `bootstrap_host`,
    /// publishes the registry root and coord1's stream, and returns the
    /// fleet with `host_b` a second clone that has never synchronized.
    ///
    /// `bootstrap_host` is a parameter rather than a constant because the
    /// live fleet's own bindings mostly say `migration` -- the placeholder
    /// the v1->v2 replay stamped, naming a host that does not exist -- and
    /// the repair path for those has to be exercised from exactly that
    /// starting state, not from a tidy one.
    fn two_host_fleet(bootstrap_host: &str) -> Fleet {
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
            short(bootstrap_host),
        )
        .unwrap();
        let fleet = Fleet {
            origin,
            host_a,
            host_b: init_repo(),
        };
        publish_registry(fleet.host_a.path(), &fleet.remote());
        crate::coordinator::drain_and_publish(
            fleet.host_a.path(),
            fleet.host_a.path(),
            &coord1,
            &short(bootstrap_host),
            0,
            &fleet.remote(),
        )
        .unwrap();
        fleet
    }

    /// Pushes `repo`'s current registry tip, asserting the push was
    /// accepted. `publish` never force-pushes, so a rejection here would
    /// mean a genuinely diverged registry -- which is exactly what none of
    /// these flows may ever produce.
    fn publish_registry(repo: &Path, remote: &str) {
        let tip = crate::registry::read_registry_tip(repo).unwrap().unwrap();
        let receipt = crate::publish::publish(
            repo,
            remote,
            &[crate::publish::RefUpdate::new(
                crate::registry::REGISTRY_REF,
                tip,
            )],
        )
        .unwrap();
        assert!(
            receipt.rejected.is_empty() && receipt.not_attempted.is_empty(),
            "the registry push must be a plain fast-forward: {receipt:?}"
        );
    }

    fn current_epoch(repo: &Path) -> crate::registry::RosterEpoch {
        let tip = crate::registry::read_registry_tip(repo).unwrap().unwrap();
        crate::registry::read_epoch(repo, &tip).unwrap()
    }

    fn registered_candidate(agent: &Agent, role: Role) -> Candidate {
        let data = EventData::AgentRegistered(crate::events::AgentRegistered {
            display_name: short(agent.as_str()),
            primary_role: role,
            purpose: text("takes part in the two-host fixture"),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        Candidate::new(agent, &data, vec![])
    }

    /// A member dropped from the roster keeps its stream loaded, so the
    /// events that reference it still reduce.
    ///
    /// Reduction used to load only `epoch.active_members`, the *current*
    /// roster. A published stream is immutable and other agents' events cite
    /// it by id forever, so the moment a roster transition drops a member,
    /// every `require_agent` naming them, every `require_role` on them as a
    /// co-author or reviewer, and every cross-stream `refs` lookup into their
    /// history stops resolving. Those are `Err` inside `apply::reduce`, which
    /// propagates on the first one with no per-event isolation -- so an
    /// ordinary retirement would take the whole bus down, on every host,
    /// permanently, since the log is append-only and the citing events cannot
    /// be withdrawn.
    ///
    /// The file already made this argument for *epochs* -- "a complete
    /// frontier authored against an older epoch must remain re-validatable
    /// forever" -- and simply never extended it to the members inside them.
    ///
    /// `host_b` has never synchronized, so this exercises the fetch path as
    /// well as the reduction: fetching only the current roster would leave
    /// the dropped member's stream absent locally, which fails exactly the
    /// same way as not loading a stream that is present.
    #[test]
    fn a_member_dropped_from_the_roster_still_has_its_stream_reduced() {
        let fleet = two_host_fleet("host1");
        let coord1 = a("coord1");
        let alice = a("alice");

        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &alice,
            Role::Implementor,
            "host1",
        );

        // coord1 publishes an event that names alice, so her absence is not
        // merely a smaller state but an unresolvable reference.
        let issue = EventData::IssueOpened(crate::events::IssueOpened {
            target: alice.clone(),
            issue_kind: crate::events::IssueKind::Bug,
            severity: crate::common::Priority::Normal,
            summary: text("an issue naming a member who is later dropped"),
            code_commit: None,
            locations: vec![],
            expected: None,
            observed_behavior: None,
            reproduction: vec![],
            blocks: Default::default(),
            evidence: Default::default(),
        });
        crate::outbox::submit(
            fleet.host_a.path(),
            "client-issue",
            &Candidate::new(&coord1, &issue, vec![]),
        )
        .unwrap();
        let (drained, _receipt) = crate::coordinator::drain_and_publish(
            fleet.host_a.path(),
            fleet.host_a.path(),
            &coord1,
            &short("host1"),
            0,
            &fleet.remote(),
        )
        .unwrap();
        assert!(drained.rejected.is_empty(), "{:?}", drained.rejected);

        // Now drop alice from the roster entirely -- an epoch transition that
        // removes a member, which section 2.1 names as retirement.
        let epoch = current_epoch(fleet.host_a.path());
        let mut members = epoch.active_members.clone();
        members.remove(&alice);
        crate::registry::propose_transition(fleet.host_a.path(), &epoch, members).unwrap();
        publish_registry(fleet.host_a.path(), &fleet.remote());

        // A host that has never synchronized must still be able to read the
        // bus. Before the fix this failed with "unregistered agent: alice".
        let snap = synced_snapshot(fleet.host_b.path(), fleet.host_b.path(), &fleet.remote())
            .expect("dropping a member must not make the bus unreadable");

        assert!(
            !snap.roster_epoch.is_active_member(&alice),
            "alice really is off the current roster"
        );
        assert!(
            snap.state.agents.contains_key(&alice),
            "and her stream is still reduced, so events naming her resolve"
        );
    }

    fn retired_candidate(
        coordinator: &Agent,
        target: &Agent,
        previous_lifecycle: &crate::scalars::EventId,
    ) -> Candidate {
        let data = EventData::AgentRetired(crate::events::AgentRetired {
            target: target.clone(),
            previous_lifecycle: previous_lifecycle.clone(),
            reason: text("no longer reachable"),
            user_authority: text("operator"),
        });
        Candidate::new(coordinator, &data, vec![])
    }

    /// Registers `agent` bound to `host`, from `repo`: the registry epoch
    /// transition, the agent's own `agent.registered` event, and the
    /// publication of both -- what `cli::register` does, minus the CLI
    /// plumbing (which resolves its paths from a real process working
    /// directory and so cannot be driven in-process).
    fn register_on_host(fleet: &Fleet, repo: &Path, agent: &Agent, role: Role, host: &str) {
        let epoch = current_epoch(repo);
        let mut members = epoch.active_members.clone();
        members.insert(
            agent.clone(),
            crate::registry::MemberBinding {
                role,
                host: short(host),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        crate::registry::propose_transition(repo, &epoch, members).unwrap();
        crate::outbox::submit(repo, "client-1", &registered_candidate(agent, role)).unwrap();
        let (drained, receipt) = crate::coordinator::drain_and_publish(
            repo,
            repo,
            agent,
            &short(host),
            0,
            &fleet.remote(),
        )
        .unwrap();
        assert!(
            drained.rejected.is_empty(),
            "{agent}'s registration was rejected: {:?}",
            drained.rejected
        );
        assert!(receipt.rejected.is_empty(), "{receipt:?}");
        publish_registry(repo, &fleet.remote());
    }

    /// Gate 19 and section 2.1's "an agent may move between hosts without
    /// changing its stream identity", end to end across two real clones.
    ///
    /// This is the operation that repairs a binding whose host is wrong --
    /// including the thirteen live members still carrying the `migration`
    /// placeholder, which is what this fixture starts from. Running it on
    /// two hosts is the point: the *taking* host proposes the succession
    /// (section 2.4: "the standby or an authorized coordinator on another
    /// host proposes the registry succession by compare-and-swap"), and
    /// only the winner of that transition may then advance the stream.
    #[test]
    fn custody_moves_from_a_placeholder_host_to_a_real_one_across_two_hosts() {
        let fleet = two_host_fleet("migration");
        let coord1 = a("coord1");
        let remote = fleet.remote();

        // The starting state, and why it needs repairing: the only host
        // name that can publish is the placeholder, so the fleet is forced
        // to keep asserting a host that does not exist.
        let err = crate::coordinator::drain_outbox(
            fleet.host_a.path(),
            fleet.host_a.path(),
            &coord1,
            &short("host1"),
            0,
            &remote,
        )
        .unwrap_err();
        assert!(err.to_string().contains("custody"), "{err}");

        // host_b learns the roster the ordinary way -- by synchronizing,
        // not by sharing host_a's object store.
        synced_snapshot(fleet.host_b.path(), fleet.host_b.path(), &remote).unwrap();
        assert_eq!(
            current_epoch(fleet.host_b.path()).active_members[&coord1].host,
            short("migration")
        );

        // A coordinator repairs its own binding: section 2.4 authorizes
        // "the standby or an authorized coordinator" to propose, and coord1
        // is a coordinator in this epoch. No other identity here could --
        // see `only_a_standby_or_a_coordinator_may_repair_a_binding`.
        let epoch = current_epoch(fleet.host_b.path());
        crate::registry::propose_custody_succession(
            fleet.host_b.path(),
            &epoch,
            &coord1,
            &coord1,
            short("host2"),
        )
        .unwrap();
        publish_registry(fleet.host_b.path(), &remote);

        let repaired = current_epoch(fleet.host_b.path());
        assert_eq!(repaired.active_members[&coord1].host, short("host2"));
        assert_eq!(
            repaired.active_members[&coord1].coordinator_custody_epoch, 1,
            "succession advances the custody epoch by exactly one"
        );

        // host_b, the new custodian, publishes for coord1.
        crate::outbox::submit(
            fleet.host_b.path(),
            "client-b",
            &status_candidate(&coord1, "now published from host2"),
        )
        .unwrap();
        let (drained, receipt) = crate::coordinator::drain_and_publish(
            fleet.host_b.path(),
            fleet.host_b.path(),
            &coord1,
            &short("host2"),
            1,
            &remote,
        )
        .unwrap();
        assert_eq!(drained.published.len(), 1, "{drained:?}");
        assert!(
            receipt.rejected.is_empty() && receipt.not_attempted.is_empty(),
            "the successor's stream push is an ordinary fast-forward, never a force: {receipt:?}"
        );

        // Gate 7: the superseded custodian fails closed -- under the old
        // host name, under the new host's name it does not own, and under
        // the new name at a custody epoch it does not hold.
        synced_snapshot(fleet.host_a.path(), fleet.host_a.path(), &remote).unwrap();
        for (host, custody) in [("migration", 0), ("host2", 0), ("migration", 1)] {
            let err = crate::coordinator::drain_outbox(
                fleet.host_a.path(),
                fleet.host_a.path(),
                &coord1,
                &short(host),
                custody,
                &remote,
            )
            .unwrap_err();
            assert!(
                err.to_string().contains("custody"),
                "{host} at custody epoch {custody} must fail closed: {err}"
            );
        }

        // And the fleet still reduces, from the host that did not make the
        // change and only learned of it by fetching.
        let snap = synced_snapshot(fleet.host_a.path(), fleet.host_a.path(), &remote).unwrap();
        assert_eq!(snap.state.agents[&coord1].next_seq, 2);
        assert_eq!(
            snap.state.agents[&coord1].status_note.as_str(),
            "now published from host2"
        );
    }

    /// Section 2.4's authorization rule for custody, stated as a refusal:
    /// an ordinary agent cannot correct its own host binding, because
    /// custody is not the agent's to move. Only "the standby or an
    /// authorized coordinator" may propose.
    ///
    /// This is the half of the binding-repair story an operator most needs:
    /// the thirteen `migration` bindings cannot be fixed by the agents
    /// themselves, and no agent-side command exists (or should) for it.
    #[test]
    fn only_a_standby_or_a_coordinator_may_repair_a_binding() {
        let fleet = two_host_fleet("migration");
        let (coord1, alice, dave) = (a("coord1"), a("alice"), a("dave"));
        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &alice,
            Role::Implementor,
            "migration",
        );
        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &dave,
            Role::Implementor,
            "migration",
        );

        let epoch = current_epoch(fleet.host_a.path());
        // alice is neither a coordinator nor her own standby.
        let err = crate::registry::propose_custody_succession(
            fleet.host_a.path(),
            &epoch,
            &alice,
            &alice,
            short("host1"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("not authorized"), "{err}");
        // Nor may she take someone else's.
        let err = crate::registry::propose_custody_succession(
            fleet.host_a.path(),
            &epoch,
            &alice,
            &dave,
            short("host1"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("not authorized"), "{err}");
        // The registry must be untouched by either refusal.
        assert_eq!(current_epoch(fleet.host_a.path()).id, epoch.id);

        // A coordinator may, on the agent's behalf -- the only repair path
        // the design gives for the `migration` bindings.
        crate::registry::propose_custody_succession(
            fleet.host_a.path(),
            &epoch,
            &coord1,
            &alice,
            short("host1"),
        )
        .unwrap();
        assert_eq!(
            current_epoch(fleet.host_a.path()).active_members[&alice].host,
            short("host1")
        );
    }

    /// Adding a host, from the new host's own clone: it registers an agent
    /// bound to itself, publishes the registry transition and the stream
    /// root, and the *other* host then reduces the result without wedging.
    ///
    /// The second half is what a single-repository test cannot check at
    /// all: host_a never observed the transition being made and reaches it
    /// only through `synced_snapshot`.
    #[test]
    fn a_new_host_can_register_an_agent_that_the_other_host_then_reduces() {
        let fleet = two_host_fleet("host1");
        let (coord1, coord2) = (a("coord1"), a("coord2"));
        let remote = fleet.remote();

        synced_snapshot(fleet.host_b.path(), fleet.host_b.path(), &remote).unwrap();
        register_on_host(
            &fleet,
            fleet.host_b.path(),
            &coord2,
            Role::Coordinator,
            "host2",
        );

        let snap = synced_snapshot(fleet.host_a.path(), fleet.host_a.path(), &remote).unwrap();
        assert!(snap.roster_epoch.is_active_member(&coord2));
        assert_eq!(
            snap.roster_epoch.active_members[&coord2].host,
            short("host2")
        );
        assert!(snap.state.agents.contains_key(&coord2));
        assert!(snap.state.agents.contains_key(&coord1));

        // The new host's coordinator holds real coordinator authority on
        // the old host's reduced view too, not merely a roster entry: it
        // publishes a coordinator-authority event and host_a reduces it.
        let alice = a("alice");
        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &alice,
            Role::Implementor,
            "host1",
        );
        synced_snapshot(fleet.host_b.path(), fleet.host_b.path(), &remote).unwrap();
        crate::outbox::submit(
            fleet.host_b.path(),
            "client-b",
            &retired_candidate(&coord2, &alice, &crate::scalars::EventId::new(&alice, 0)),
        )
        .unwrap();
        let (drained, _) = crate::coordinator::drain_and_publish(
            fleet.host_b.path(),
            fleet.host_b.path(),
            &coord2,
            &short("host2"),
            0,
            &remote,
        )
        .unwrap();
        assert!(drained.rejected.is_empty(), "{drained:?}");

        let snap = synced_snapshot(fleet.host_a.path(), fleet.host_a.path(), &remote).unwrap();
        assert!(snap.state.agents[&alice].retired);
    }

    /// The fleet-wide outage `apply::require_bootstrap_coordinator` used to
    /// carry, reproduced through the real publication and synchronization
    /// path rather than by hand-driving `apply_event`.
    ///
    /// `zed-coord` publishes a coordinator-authority event; `coord1` later
    /// retires `zed-coord`. Both are ordinary, published, immutable facts.
    /// `topological_order` breaks ties by `EventId`, so `coord1:N` sorts
    /// ahead of `zed-coord:1` on *every* host -- the retirement is applied
    /// first everywhere, and the old `require_active_role` check then
    /// rejected `zed-coord`'s own already-published event. Not a race with
    /// an unlucky order: a deterministic, permanent, fleet-wide inability
    /// to read the bus at all, on both hosts, caused by an ordinary
    /// retirement.
    ///
    /// The names are chosen so the tie-break lands that way. Spelled with
    /// the retiring coordinator sorting *after*, the identical scenario
    /// passes even unfixed -- which is why nothing already here caught it.
    ///
    /// Falsification: restoring `require_active_role(state, a,
    /// Role::Coordinator)` in `require_bootstrap_coordinator` fails both
    /// `synced_snapshot` calls below with "zed-coord is not active".
    #[test]
    fn retiring_a_coordinator_does_not_make_its_published_history_unreducible() {
        let fleet = two_host_fleet("host1");
        let (coord1, zed, alice) = (a("coord1"), a("zed-coord"), a("alice"));
        let remote = fleet.remote();
        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &zed,
            Role::Coordinator,
            "host1",
        );
        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &alice,
            Role::Implementor,
            "host1",
        );

        // zed-coord, while active, retires alice.
        crate::outbox::submit(
            fleet.host_a.path(),
            "client-a",
            &retired_candidate(&zed, &alice, &crate::scalars::EventId::new(&alice, 0)),
        )
        .unwrap();
        let (drained, _) = crate::coordinator::drain_and_publish(
            fleet.host_a.path(),
            fleet.host_a.path(),
            &zed,
            &short("host1"),
            0,
            &remote,
        )
        .unwrap();
        assert!(drained.rejected.is_empty(), "{drained:?}");

        // coord1 then retires zed-coord -- an ordinary act, not a
        // contrivance: it is how a host that is going away hands over.
        crate::outbox::submit(
            fleet.host_a.path(),
            "client-a",
            &retired_candidate(&coord1, &zed, &crate::scalars::EventId::new(&zed, 0)),
        )
        .unwrap();
        let (drained, _) = crate::coordinator::drain_and_publish(
            fleet.host_a.path(),
            fleet.host_a.path(),
            &coord1,
            &short("host1"),
            0,
            &remote,
        )
        .unwrap();
        assert!(drained.rejected.is_empty(), "{drained:?}");

        for (label, repo) in [
            ("publisher", fleet.host_a.path()),
            ("peer", fleet.host_b.path()),
        ] {
            let snap = synced_snapshot(repo, repo, &remote)
                .unwrap_or_else(|e| panic!("{label} must still be able to read the bus: {e}"));
            assert!(snap.state.agents[&zed].retired, "{label}");
            assert!(
                snap.state.agents[&alice].retired,
                "{label}: the retired coordinator's own published act still stands"
            );
        }
    }

    /// The publication-time half of that relocation
    /// (`coordinator::verify_author_active`): replay no longer asks whether
    /// a coordinator is live, so the gate where the question *does* have
    /// one answer must. A retired coordinator submitting a *new*
    /// coordinator-authority event is refused with a durable receipt,
    /// leaving the rest of its batch alone.
    ///
    /// Falsification: deleting the `verify_author_active` call in
    /// `drain_outbox` publishes zed-coord's second retirement instead of
    /// rejecting it.
    #[test]
    fn a_retired_coordinator_cannot_publish_a_new_coordinator_authority_event() {
        let fleet = two_host_fleet("host1");
        let (coord1, zed, alice) = (a("coord1"), a("zed-coord"), a("alice"));
        let remote = fleet.remote();
        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &zed,
            Role::Coordinator,
            "host1",
        );
        register_on_host(
            &fleet,
            fleet.host_a.path(),
            &alice,
            Role::Implementor,
            "host1",
        );

        crate::outbox::submit(
            fleet.host_a.path(),
            "client-a",
            &retired_candidate(&coord1, &zed, &crate::scalars::EventId::new(&zed, 0)),
        )
        .unwrap();
        crate::coordinator::drain_and_publish(
            fleet.host_a.path(),
            fleet.host_a.path(),
            &coord1,
            &short("host1"),
            0,
            &remote,
        )
        .unwrap();

        // Now retired, zed-coord tries to retire alice. An ordinary status
        // event rides along to prove the refusal is candidate-scoped and
        // does not abort the whole drain. Distinct client ids: `submit` is
        // an atomic overwrite keyed by client id, so reusing one here would
        // silently leave a single candidate in the outbox.
        crate::outbox::submit(
            fleet.host_a.path(),
            "client-retire",
            &retired_candidate(&zed, &alice, &crate::scalars::EventId::new(&alice, 0)),
        )
        .unwrap();
        crate::outbox::submit(
            fleet.host_a.path(),
            "client-status",
            &status_candidate(&zed, "still talking"),
        )
        .unwrap();
        let (drained, _) = crate::coordinator::drain_and_publish(
            fleet.host_a.path(),
            fleet.host_a.path(),
            &zed,
            &short("host1"),
            0,
            &remote,
        )
        .unwrap();
        assert_eq!(drained.rejected.len(), 1, "{drained:?}");
        assert_eq!(drained.rejected[0].kind, "agent.retired");
        assert!(
            drained.rejected[0]
                .reason
                .contains("retired or otherwise inactive"),
            "{:?}",
            drained.rejected[0]
        );
        assert_eq!(
            drained.published.len(),
            1,
            "the ordinary status event still publishes"
        );

        let snap = synced_snapshot(fleet.host_b.path(), fleet.host_b.path(), &remote).unwrap();
        assert!(!snap.state.agents[&alice].retired);
    }
}
