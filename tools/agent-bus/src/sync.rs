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

use crate::error::{invalid, AbResult};
use crate::registry::RosterEpoch;
use crate::scalars::{Agent, ObjectId};
use crate::state::BusState;
use std::collections::BTreeMap;
use std::path::Path;

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
/// against, not merely diagnostic), and how fresh it is.
#[derive(Debug, Clone)]
pub struct Snapshot {
    pub state: BusState,
    pub roster_epoch: RosterEpoch,
    pub stream_tips: BTreeMap<Agent, ObjectId>,
    pub freshness: Freshness,
}

/// Reduces whatever is already local -- no network round trip -- into a
/// `Snapshot` marked `Cached`. Fails if the registry has never been created
/// locally at all.
pub fn cached_snapshot(repo: &Path, worktrees_dir: &Path) -> AbResult<Snapshot> {
    reduce_local(repo, worktrees_dir, Freshness::Cached)
}

/// Fetches the registry ref, then every currently active member's stream
/// ref, from `remote` into their ordinary local branch refs (a plain,
/// non-force fetch -- see `gitrepo::fetch_refspecs`'s own doc for why that
/// alone is enough to reject an unexpected remote history rewrite), and
/// reduces the result into a `Snapshot` marked `CurrentAsOfRemoteProbe`.
/// The registry must be fetched first: it is what decides which stream
/// refs to fetch next.
pub fn synced_snapshot(repo: &Path, remote: &str, worktrees_dir: &Path) -> AbResult<Snapshot> {
    let registry_refspec = format!(
        "{0}:{0}",
        crate::registry::REGISTRY_REF
    );
    crate::gitrepo::fetch_refspecs(repo, remote, &[registry_refspec])?;

    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists on the remote"))?;
    let epoch = crate::registry::read_epoch(
        repo,
        &registry_tip,
        &worktrees_dir.join("_sync_epoch"),
    )?;

    let stream_refspecs: Vec<String> = epoch
        .active_members
        .keys()
        .map(|agent| {
            let r = crate::stream::stream_ref(agent).into_string();
            format!("{r}:{r}")
        })
        .collect();
    if !stream_refspecs.is_empty() {
        crate::gitrepo::fetch_refspecs(repo, remote, &stream_refspecs)?;
    }

    reduce_local(repo, worktrees_dir, Freshness::CurrentAsOfRemoteProbe)
}

fn reduce_local(repo: &Path, worktrees_dir: &Path, freshness: Freshness) -> AbResult<Snapshot> {
    let registry_tip = crate::registry::read_registry_tip(repo)?
        .ok_or_else(|| invalid("no registry root exists locally"))?;
    let epoch = crate::registry::read_epoch(
        repo,
        &registry_tip,
        &worktrees_dir.join("_reduce_epoch"),
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

    let state = crate::apply::reduce(config, Some(epoch.clone()), &streams)?;
    Ok(Snapshot {
        state,
        roster_epoch: epoch,
        stream_tips,
        freshness,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{AgentStatusEvent, EventData, LifecycleStatus};
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

    #[test]
    fn cached_snapshot_fails_before_any_registry_exists() {
        let repo = init_repo();
        let err = cached_snapshot(repo.path(), &repo.path().join("_wt")).unwrap_err();
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

        let snap = cached_snapshot(repo.path(), &repo.path().join("_snap_wt")).unwrap();
        assert_eq!(snap.freshness, Freshness::Cached);
        assert!(snap.roster_epoch.is_active_member(&coord1));
        assert!(snap.state.agents.contains_key(&coord1));
        assert_eq!(snap.stream_tips.len(), 1);
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
        let snap = synced_snapshot(
            host_b.path(),
            &origin.path().to_string_lossy(),
            &host_b.path().join("_sync_wt"),
        )
        .unwrap();
        assert_eq!(snap.freshness, Freshness::CurrentAsOfRemoteProbe);
        assert!(snap.roster_epoch.is_active_member(&coord1));
        let agent_state = snap.state.agents.get(&coord1).unwrap();
        assert_eq!(agent_state.next_seq, 2); // registration + the one status event
    }

    #[test]
    fn synced_snapshot_fails_when_the_remote_has_no_registry_yet() {
        let origin = init_bare_origin();
        let repo = init_repo();
        let err = synced_snapshot(
            repo.path(),
            &origin.path().to_string_lossy(),
            &repo.path().join("_sync_wt"),
        )
        .unwrap_err();
        assert!(err.to_string().contains("no registry root"), "{err}");
    }
}
