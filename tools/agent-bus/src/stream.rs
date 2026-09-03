//! Per-agent event streams (docs/AGENT_COORDINATION_EVOLUTION.md section 2.1).
//!
//! Every agent identity owns one append-only, single-writer git ref:
//! `refs/heads/agent-events/<agent>`. Its root commit is a canonical stream
//! header naming provenance (the version-two activation event on the
//! version-one bus, this identity's registration authority, the final
//! version-one sequence it consumed if migrated, object format, and schema
//! fingerprint). The stream then contains only that agent's segmented JSONL
//! (`storage.rs`) and the header. A stream commit has exactly one parent,
//! changes only its owner's stream paths, and introduces a contiguous
//! suffix of new events.
//!
//! This module owns the git-ref-level mechanics: naming, header shape,
//! constructing a stream's root or a follow-on commit in a local worktree,
//! and the local half of custody protection (gate 6 -- refusing to build a
//! non-fast-forward-shaped commit in the first place). Remote protection
//! (denying a non-fast-forward *push*, and reconciling two coordinators
//! racing for the same custody epoch) belongs to the coordinator layer that
//! actually performs the push, not here.

use crate::envelope::Envelope;
use crate::error::{invalid, AbError, AbResult};
use crate::scalars::{Agent, Branch, EventId, ObjectId};
use serde::{Deserialize, Serialize};
use std::path::Path;

pub const STREAM_REF_PREFIX: &str = "refs/heads/agent-events/";

/// The agent grammar (`[a-z][a-z0-9-]{0,47}`) is already a valid single ref
/// component, so this can never fail `Branch::parse`.
pub fn stream_ref(agent: &Agent) -> Branch {
    Branch::parse(format!("{STREAM_REF_PREFIX}{agent}")).expect("agent name is a valid ref component")
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StreamHeader {
    pub agent: Agent,
    pub activation_event: EventId,
    pub registration_authority: EventId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub final_v1_seq: Option<u64>,
    pub object_format: String,
    pub schema_fingerprint: String,
}

const HEADER_FILE: &str = "header.json";

impl StreamHeader {
    fn to_canonical_bytes(&self) -> Vec<u8> {
        // Reuses the same canonical-JSON discipline as the envelope: pass
        // through `serde_json::Value` so keys sort via its `BTreeMap`-backed
        // `Map`, then a compact re-serialization.
        let value = serde_json::to_value(self).expect("StreamHeader always serializable");
        serde_json::to_vec(&value).expect("StreamHeader value always serializable")
    }

    fn parse(bytes: &[u8]) -> AbResult<StreamHeader> {
        serde_json::from_slice(bytes).map_err(|e| invalid(format!("malformed stream header: {e}")))
    }
}

/// The current tip of `agent`'s stream, or `None` if it has never been
/// created.
pub fn read_stream_tip(repo: &Path, agent: &Agent) -> AbResult<Option<ObjectId>> {
    match crate::gitrepo::rev_parse_opt(repo, stream_ref(agent).as_str())? {
        Some(s) => Ok(Some(ObjectId::parse(s)?)),
        None => Ok(None),
    }
}

fn read_header(worktree: &Path) -> AbResult<StreamHeader> {
    let bytes = std::fs::read(worktree.join(HEADER_FILE)).map_err(|e| AbError::Io {
        path: worktree.join(HEADER_FILE).display().to_string(),
        source: e,
    })?;
    StreamHeader::parse(&bytes)
}

/// Reads and structurally validates the full stream for `agent`: the header
/// plus every event, in order. Does not itself check frontier completeness,
/// registry membership, or custody -- see `frontier.rs`/`registry.rs` for
/// that, applied by the caller once it has the registry epoch this stream's
/// events claim to observe.
pub fn read_stream(
    repo: &Path,
    agent: &Agent,
    worktrees_dir: &Path,
) -> AbResult<(StreamHeader, Vec<Envelope>)> {
    let tip = read_stream_tip(repo, agent)?
        .ok_or_else(|| invalid(format!("{agent} has no stream")))?;
    let worktree = worktrees_dir.join(format!("stream-read-{agent}"));
    crate::gitrepo::ensure_bus_worktree(repo, &worktree, tip.as_str())?;
    let header = read_header(&worktree)?;
    if header.agent != *agent {
        return Err(invalid(format!(
            "{agent}'s stream header names agent {}",
            header.agent
        )));
    }
    let log = crate::storage::read_stream_log(&worktree, agent)?;
    Ok((header, log))
}

/// Creates `agent`'s stream root commit: header plus the first envelope
/// (which must be `agent.registered` at sequence zero -- `storage::
/// read_stream_log` already enforces this on read, so a malformed root would
/// fail the very next read rather than silently succeed). Returns the new
/// commit id. Does not push; publication is the coordinator's job.
pub fn create_root_commit(
    repo: &Path,
    header: &StreamHeader,
    first_event: &Envelope,
    worktree: &Path,
) -> AbResult<ObjectId> {
    if read_stream_tip(repo, &header.agent)?.is_some() {
        return Err(invalid(format!(
            "{}'s stream already exists; cannot create a second root",
            header.agent
        )));
    }
    if first_event.seq != 0 || first_event.kind != "agent.registered" {
        return Err(invalid(
            "a stream's root commit must introduce agent.registered at sequence zero",
        ));
    }
    std::fs::create_dir_all(worktree).map_err(|e| AbError::Io {
        path: worktree.display().to_string(),
        source: e,
    })?;
    // An orphan worktree: no start point, so the first commit here has no
    // parent, matching the design's "each stream is an orphan history."
    let tmp_branch = format!("_tmp_stream_root_{}", header.agent);
    crate::gitrepo::run_ok(
        repo,
        &[
            "worktree",
            "add",
            "--orphan",
            "-b",
            &tmp_branch,
            &worktree.to_string_lossy(),
        ],
    )?;
    // Segments are strict LF-only (`storage.rs`'s structural checks reject a
    // CR byte outright), but a checkout on a machine with `core.autocrlf`
    // enabled (the common Windows default) would otherwise silently rewrite
    // LF to CRLF when this commit is later checked out by `read_stream`/
    // `append_to_stream`. Committing `.gitattributes` marking these paths
    // `-text` once, here in the root commit, governs every later checkout of
    // this stream regardless of the checking-out machine's own config.
    crate::storage::atomic_write(
        &worktree.join(".gitattributes"),
        b"*.jsonl -text\nheader.json -text\n",
    )?;
    crate::storage::atomic_write(&worktree.join(HEADER_FILE), &header.to_canonical_bytes())?;
    crate::storage::append_event(worktree, first_event)?;
    crate::gitrepo::add_all(worktree)?;
    let commit = crate::gitrepo::commit(
        worktree,
        &format!("agent-events: {} stream root", header.agent),
    )?;
    crate::gitrepo::run_ok(
        repo,
        &[
            "branch",
            "-f",
            stream_ref(&header.agent).as_str(),
            &commit,
        ],
    )?;
    crate::gitrepo::run_ok(
        repo,
        &["worktree", "remove", "--force", &worktree.to_string_lossy()],
    )?;
    crate::gitrepo::run_ok(repo, &["branch", "-D", &tmp_branch])?;
    ObjectId::parse(commit)
}

/// Appends `new_events` (already carrying correct, contiguous sequence
/// numbers continuing from the stream's current tail) to `agent`'s stream,
/// producing exactly one new commit whose sole parent is the stream's
/// current tip. Returns the new commit id. Does not push.
///
/// Gate 6's local half: if the stream has moved since `expected_parent` was
/// read (a concurrent or stale writer), this refuses to build the commit at
/// all rather than silently rebasing onto whatever is there now -- "the
/// loser stops and resolves custody" (section 2.1), not merges through it.
pub fn append_to_stream(
    repo: &Path,
    agent: &Agent,
    expected_parent: &ObjectId,
    new_events: &[Envelope],
    worktree: &Path,
) -> AbResult<ObjectId> {
    let actual_tip = read_stream_tip(repo, agent)?
        .ok_or_else(|| invalid(format!("{agent} has no stream to append to")))?;
    if &actual_tip != expected_parent {
        return Err(invalid(format!(
            "{agent}'s stream has moved: expected parent {expected_parent}, actual tip {actual_tip} \
             -- stale or duplicate custody, not routine contention; resolve custody before retrying"
        )));
    }
    if new_events.is_empty() {
        return Err(invalid("append_to_stream requires at least one event"));
    }
    for e in new_events {
        if e.agent != *agent {
            return Err(invalid(format!(
                "event {} does not belong to {agent}'s stream",
                e.id
            )));
        }
    }
    crate::gitrepo::ensure_bus_worktree(repo, worktree, expected_parent.as_str())?;
    crate::gitrepo::checkout_detach(worktree, expected_parent.as_str())?;
    for e in new_events {
        crate::storage::append_event(worktree, e)?;
    }
    crate::gitrepo::add_all(worktree)?;
    let commit = crate::gitrepo::commit(
        worktree,
        &format!(
            "agent-events: {agent} +{} event(s) through {}",
            new_events.len(),
            new_events.last().unwrap().id
        ),
    )?;

    // Defensive re-check of "changes only its owner's stream paths": every
    // changed path from expected_parent..commit must be a segment file (the
    // header never changes after the root commit).
    for (_, path) in crate::gitrepo::diff_name_status(repo, expected_parent.as_str(), &commit)? {
        if path == HEADER_FILE {
            return Err(invalid(
                "a follow-on stream commit must not modify the stream header",
            ));
        }
        if !path.ends_with(".jsonl") {
            return Err(invalid(format!(
                "a stream commit touched an unexpected path: {path}"
            )));
        }
    }
    let parents = crate::gitrepo::parents_of(repo, &commit)?;
    if parents != vec![expected_parent.as_str().to_string()] {
        return Err(invalid(format!(
            "stream commit {commit} does not have exactly one parent equal to {expected_parent}"
        )));
    }

    crate::gitrepo::run_ok(repo, &["branch", "-f", stream_ref(agent).as_str(), &commit])?;
    ObjectId::parse(commit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{AgentRegistered, AgentStatusEvent, EventData, LifecycleStatus, Role};
    use crate::frontier::ObservedFrontier;
    use crate::scalars::{Short, Text};

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

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn hash(n: u64) -> ObjectId {
        ObjectId::parse(format!("{n:040x}")).unwrap()
    }

    fn no_frontier() -> ObservedFrontier {
        ObservedFrontier::sparse(hash(1), [])
    }

    fn header(agent: &Agent) -> StreamHeader {
        StreamHeader {
            agent: agent.clone(),
            activation_event: EventId::new(&a("coord1"), 0),
            registration_authority: EventId::new(agent, 0),
            final_v1_seq: None,
            object_format: "sha1".to_string(),
            schema_fingerprint: "test-fingerprint".to_string(),
        }
    }

    fn registered_envelope(agent: &Agent, seq: u64) -> Envelope {
        let data = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse(agent.to_string()).unwrap(),
            primary_role: Role::Implementor,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        Envelope::new(agent, seq, no_frontier(), &data, [])
    }

    fn status_envelope(agent: &Agent, seq: u64) -> Envelope {
        let data = EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: Text::parse("going".into()).unwrap(),
            product_branch: None,
            product_commit: None,
        });
        Envelope::new(agent, seq, no_frontier(), &data, [])
    }

    #[test]
    fn stream_ref_names_the_expected_ref() {
        assert_eq!(
            stream_ref(&a("alice")).as_str(),
            "refs/heads/agent-events/alice"
        );
    }

    #[test]
    fn read_stream_tip_is_none_before_creation() {
        let repo = init_repo();
        assert_eq!(read_stream_tip(repo.path(), &a("alice")).unwrap(), None);
    }

    #[test]
    fn create_root_commit_then_read_stream_round_trips() {
        let repo = init_repo();
        let alice = a("alice");
        let wt = repo.path().join("_wt_root");
        let commit = create_root_commit(repo.path(), &header(&alice), &registered_envelope(&alice, 0), &wt)
            .unwrap();
        assert_eq!(
            read_stream_tip(repo.path(), &alice).unwrap(),
            Some(commit.clone())
        );

        let reads_dir = repo.path().join("_wt_reads");
        let (read_header, log) = read_stream(repo.path(), &alice, &reads_dir).unwrap();
        assert_eq!(read_header, header(&alice));
        assert_eq!(log.len(), 1);
        assert_eq!(log[0].kind, "agent.registered");
    }

    #[test]
    fn create_root_commit_rejects_a_second_root() {
        let repo = init_repo();
        let alice = a("alice");
        let wt = repo.path().join("_wt_root");
        create_root_commit(repo.path(), &header(&alice), &registered_envelope(&alice, 0), &wt).unwrap();
        let wt2 = repo.path().join("_wt_root2");
        let err = create_root_commit(repo.path(), &header(&alice), &registered_envelope(&alice, 0), &wt2)
            .unwrap_err();
        assert!(err.to_string().contains("already exists"), "{err}");
    }

    #[test]
    fn create_root_commit_rejects_a_first_event_that_is_not_agent_registered() {
        let repo = init_repo();
        let alice = a("alice");
        let wt = repo.path().join("_wt_root");
        let err = create_root_commit(repo.path(), &header(&alice), &status_envelope(&alice, 0), &wt)
            .unwrap_err();
        assert!(err.to_string().contains("agent.registered"), "{err}");
    }

    #[test]
    fn append_to_stream_extends_with_exactly_one_new_commit() {
        let repo = init_repo();
        let alice = a("alice");
        let wt = repo.path().join("_wt_root");
        let root = create_root_commit(repo.path(), &header(&alice), &registered_envelope(&alice, 0), &wt)
            .unwrap();

        let append_wt = repo.path().join("_wt_append");
        let new_tip = append_to_stream(
            repo.path(),
            &alice,
            &root,
            &[status_envelope(&alice, 1)],
            &append_wt,
        )
        .unwrap();
        assert_eq!(read_stream_tip(repo.path(), &alice).unwrap(), Some(new_tip.clone()));
        assert_eq!(
            crate::gitrepo::parents_of(repo.path(), new_tip.as_str()).unwrap(),
            vec![root.as_str().to_string()]
        );

        let reads_dir = repo.path().join("_wt_reads");
        let (_h, log) = read_stream(repo.path(), &alice, &reads_dir).unwrap();
        assert_eq!(log.len(), 2);
        assert_eq!(log[1].seq, 1);
    }

    /// Gate 6's local half: a stale `expected_parent` (the stream moved
    /// since it was read) must be refused, not silently rebased through.
    #[test]
    fn append_to_stream_rejects_a_stale_expected_parent() {
        let repo = init_repo();
        let alice = a("alice");
        let wt = repo.path().join("_wt_root");
        let root = create_root_commit(repo.path(), &header(&alice), &registered_envelope(&alice, 0), &wt)
            .unwrap();
        // Advance the stream out from under a caller still holding `root`.
        let append_wt = repo.path().join("_wt_append1");
        append_to_stream(repo.path(), &alice, &root, &[status_envelope(&alice, 1)], &append_wt).unwrap();

        let stale_wt = repo.path().join("_wt_append2");
        let err = append_to_stream(
            repo.path(),
            &alice,
            &root, // stale: the real tip has already advanced past this
            &[status_envelope(&alice, 1)],
            &stale_wt,
        )
        .unwrap_err();
        assert!(err.to_string().contains("stale or duplicate custody"), "{err}");
    }

    #[test]
    fn append_to_stream_rejects_an_event_belonging_to_a_different_agent() {
        let repo = init_repo();
        let alice = a("alice");
        let bob = a("bob");
        let wt = repo.path().join("_wt_root");
        let root = create_root_commit(repo.path(), &header(&alice), &registered_envelope(&alice, 0), &wt)
            .unwrap();
        let append_wt = repo.path().join("_wt_append");
        let err = append_to_stream(repo.path(), &alice, &root, &[status_envelope(&bob, 1)], &append_wt)
            .unwrap_err();
        assert!(err.to_string().contains("does not belong to"), "{err}");
    }

    #[test]
    fn append_to_stream_rejects_an_empty_batch() {
        let repo = init_repo();
        let alice = a("alice");
        let wt = repo.path().join("_wt_root");
        let root = create_root_commit(repo.path(), &header(&alice), &registered_envelope(&alice, 0), &wt)
            .unwrap();
        let append_wt = repo.path().join("_wt_append");
        let err = append_to_stream(repo.path(), &alice, &root, &[], &append_wt).unwrap_err();
        assert!(err.to_string().contains("at least one event"), "{err}");
    }

    #[test]
    fn read_stream_fails_for_an_agent_with_no_stream() {
        let repo = init_repo();
        let reads_dir = repo.path().join("_wt_reads");
        let err = read_stream(repo.path(), &a("nobody"), &reads_dir).unwrap_err();
        assert!(err.to_string().contains("has no stream"), "{err}");
    }
}
