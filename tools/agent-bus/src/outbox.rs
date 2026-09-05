//! The local outbox (docs/AGENT_COORDINATION_EVOLUTION.md section 2.3).
//!
//! "An agent submits an immutable candidate by atomically creating a
//! uniquely named file in its own local outbox." No lock, no network round
//! trip, and no coordinator involvement at submission time -- ordinary bus
//! work never contends on anything here (gate 1/2/8's precondition). The
//! host coordinator (built on top of this) later validates, sequences,
//! batches, and publishes what accumulates.
//!
//! Lives outside any committed tree, under `<git_common_dir>/agent-bus/
//! outbox/<agent>/`, the same "operational state, not product history"
//! location `lock.rs` already uses for its own file.

use crate::error::{invalid, AbError, AbResult};
use crate::events::EventData;
use crate::scalars::{Agent, EventId};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

/// One not-yet-sequenced candidate event, as submitted by its author. The
/// coordinator assigns the canonical `EventId`/stream position later --
/// submission itself carries no sequence number, since imposing one is
/// exactly the single-actor decision this design takes off the submission
/// path.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Candidate {
    pub agent: Agent,
    pub kind: String,
    pub data: serde_json::Value,
    pub extra_refs: Vec<EventId>,
    /// Section 2.3/2.4's urgent-flush request: "Correctness issues, review
    /// transitions, ownership changes, and urgent broadcasts request an
    /// urgent flush." A priority signal for the coordinator's batching
    /// policy, not a liveness guarantee -- `list_pending` orders urgent
    /// candidates first so a coordinator draining a mixed outbox processes
    /// (and therefore publishes) them ahead of ordinary work, but an urgent
    /// candidate that no coordinator ever drains is exactly as pending as
    /// any other (gate 18: "remains visibly pending while its coordinator
    /// is stopped").
    #[serde(default)]
    pub urgent: bool,
}

impl Candidate {
    pub fn new(agent: &Agent, data: &EventData, extra_refs: Vec<EventId>) -> Candidate {
        Candidate {
            agent: agent.clone(),
            kind: data.kind().to_string(),
            data: data.to_value(),
            extra_refs,
            urgent: false,
        }
    }

    /// Marks this candidate as urgent (see the `urgent` field's doc).
    /// Chainable: `Candidate::new(...).urgent()`.
    pub fn urgent(mut self) -> Candidate {
        self.urgent = true;
        self
    }

    pub fn typed_data(&self) -> AbResult<EventData> {
        EventData::from_kind_and_value(&self.kind, self.data.clone())
    }
}

pub fn outbox_dir(git_common_dir: &Path, agent: &Agent) -> PathBuf {
    git_common_dir
        .join("agent-bus")
        .join("outbox")
        .join(agent.as_str())
}

fn candidate_path(git_common_dir: &Path, agent: &Agent, client_id: &str) -> AbResult<PathBuf> {
    if client_id.is_empty()
        || client_id.len() > 128
        || !client_id
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
    {
        return Err(invalid(format!("invalid outbox client_id: {client_id:?}")));
    }
    Ok(outbox_dir(git_common_dir, agent).join(format!("{client_id}.json")))
}

/// Submits one candidate, keyed by a caller-chosen `client_id`. Deliberately
/// an atomic *overwrite* (not create-exclusive): the caller controls both
/// the id and the content, so retrying the same submission after a crash
/// with the same `client_id` is a safe, idempotent no-op rather than an
/// error the caller must first distinguish from "someone else already used
/// this id." Two concurrent submissions from the same agent simply use two
/// different `client_id`s -- there is nothing here for them to contend on.
pub fn submit(git_common_dir: &Path, client_id: &str, candidate: &Candidate) -> AbResult<PathBuf> {
    let dir = outbox_dir(git_common_dir, &candidate.agent);
    std::fs::create_dir_all(&dir).map_err(|e| AbError::Io {
        path: dir.display().to_string(),
        source: e,
    })?;
    let path = candidate_path(git_common_dir, &candidate.agent, client_id)?;
    let bytes = serde_json::to_vec_pretty(candidate)?;
    crate::storage::atomic_write(&path, &bytes)?;
    Ok(path)
}

/// Lists every pending candidate for `agent`, urgent candidates first
/// (section 2.3/2.4's urgent-flush request -- "priority input to that
/// policy," ties broken oldest-first by filesystem modified time within
/// each tier) -- the order the coordinator should offer them to the batch
/// builder in, though the coordinator remains free to reorder for
/// dependency closure.
pub fn list_pending(git_common_dir: &Path, agent: &Agent) -> AbResult<Vec<(PathBuf, Candidate)>> {
    let dir = outbox_dir(git_common_dir, agent);
    if !dir.exists() {
        return Ok(Vec::new());
    }
    let mut entries: Vec<(PathBuf, std::time::SystemTime)> = Vec::new();
    for entry in std::fs::read_dir(&dir).map_err(|e| AbError::Io {
        path: dir.display().to_string(),
        source: e,
    })? {
        let entry = entry.map_err(|e| AbError::Io {
            path: dir.display().to_string(),
            source: e,
        })?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let modified = entry
            .metadata()
            .and_then(|m| m.modified())
            .unwrap_or(std::time::SystemTime::UNIX_EPOCH);
        entries.push((path, modified));
    }
    entries.sort_by_key(|(_, m)| *m);
    let mut out = Vec::new();
    for (path, _) in entries {
        let bytes = std::fs::read(&path).map_err(|e| AbError::Io {
            path: path.display().to_string(),
            source: e,
        })?;
        let candidate: Candidate = serde_json::from_slice(&bytes)?;
        if candidate.agent != *agent {
            return Err(invalid(format!(
                "outbox entry {} claims agent {} but lives under {agent}'s outbox",
                path.display(),
                candidate.agent
            )));
        }
        out.push((path, candidate));
    }
    // Stable sort: within the already-established mtime order, urgent
    // candidates move to the front without disturbing relative order among
    // candidates of the same urgency.
    out.sort_by_key(|(_, c)| !c.urgent);
    Ok(out)
}

/// Removes a candidate once the coordinator has durably accepted or
/// rejected it -- an accepted candidate's outcome now lives in the stream
/// commit (or a rejection receipt); it has no further use in the outbox.
pub fn remove(path: &Path) -> AbResult<()> {
    match std::fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(e) => Err(AbError::Io {
            path: path.display().to_string(),
            source: e,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{AgentStatusEvent, LifecycleStatus};
    use crate::scalars::Text;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn status_candidate(agent: &Agent) -> Candidate {
        let data = EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: Text::parse("x".into()).unwrap(),
            product_branch: None,
            product_commit: None,
        });
        Candidate::new(agent, &data, vec![])
    }

    #[test]
    fn submit_then_list_pending_round_trips() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        let pending = list_pending(dir.path(), &alice).unwrap();
        assert_eq!(pending.len(), 1);
        assert_eq!(pending[0].1, status_candidate(&alice));
    }

    #[test]
    fn list_pending_is_empty_before_any_submission() {
        let dir = tempfile::tempdir().unwrap();
        assert!(list_pending(dir.path(), &a("alice")).unwrap().is_empty());
    }

    /// Retrying the same `client_id` after a (simulated) crash overwrites
    /// rather than duplicating -- the outbox never accumulates two entries
    /// for what the caller considers one submission.
    #[test]
    fn resubmitting_the_same_client_id_is_idempotent() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        assert_eq!(list_pending(dir.path(), &alice).unwrap().len(), 1);
    }

    #[test]
    fn two_client_ids_from_the_same_agent_both_persist() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        submit(dir.path(), "client-2", &status_candidate(&alice)).unwrap();
        assert_eq!(list_pending(dir.path(), &alice).unwrap().len(), 2);
    }

    #[test]
    fn submit_rejects_a_malformed_client_id() {
        let dir = tempfile::tempdir().unwrap();
        let err = submit(dir.path(), "has a space", &status_candidate(&a("alice"))).unwrap_err();
        assert!(
            err.to_string().contains("invalid outbox client_id"),
            "{err}"
        );
    }

    #[test]
    fn list_pending_is_ordered_oldest_first() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "first", &status_candidate(&alice)).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        submit(dir.path(), "second", &status_candidate(&alice)).unwrap();
        let pending = list_pending(dir.path(), &alice).unwrap();
        assert_eq!(pending.len(), 2);
        assert!(pending[0].0.ends_with("first.json"));
        assert!(pending[1].0.ends_with("second.json"));
    }

    #[test]
    fn remove_deletes_the_candidate_file() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        let path = submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        remove(&path).unwrap();
        assert!(list_pending(dir.path(), &alice).unwrap().is_empty());
    }

    /// Removing an already-gone file is not an error -- a retried cleanup
    /// after a crash between "wrote the stream commit" and "deleted the
    /// outbox entry" must not itself fail.
    #[test]
    fn remove_is_a_noop_for_a_missing_file() {
        let dir = tempfile::tempdir().unwrap();
        assert!(remove(&dir.path().join("nonexistent.json")).is_ok());
    }

    #[test]
    fn candidate_new_defaults_to_not_urgent() {
        let alice = a("alice");
        assert!(!status_candidate(&alice).urgent);
    }

    #[test]
    fn urgent_marks_the_candidate() {
        let alice = a("alice");
        assert!(status_candidate(&alice).urgent().urgent);
    }

    /// Gate 18's ordering half: an urgent candidate submitted *after* two
    /// ordinary ones still comes first -- urgency, not submission time, is
    /// the primary sort key.
    #[test]
    fn list_pending_puts_urgent_candidates_first_regardless_of_submission_order() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "first", &status_candidate(&alice)).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        submit(dir.path(), "second", &status_candidate(&alice)).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        submit(
            dir.path(),
            "third-urgent",
            &status_candidate(&alice).urgent(),
        )
        .unwrap();

        let pending = list_pending(dir.path(), &alice).unwrap();
        assert_eq!(pending.len(), 3);
        assert!(
            pending[0].0.ends_with("third-urgent.json"),
            "{:?}",
            pending[0].0
        );
        assert!(pending[0].1.urgent);
        // Ties within a tier keep mtime order: neither ordinary candidate
        // was reordered relative to the other.
        assert!(pending[1].0.ends_with("first.json"), "{:?}", pending[1].0);
        assert!(pending[2].0.ends_with("second.json"), "{:?}", pending[2].0);
    }

    /// Two urgent candidates among ordinary ones: both urgent ones sort
    /// ahead of every ordinary one, still oldest-urgent-first between them.
    #[test]
    fn list_pending_keeps_multiple_urgent_candidates_ordered_among_themselves() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "urgent-a", &status_candidate(&alice).urgent()).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        submit(dir.path(), "ordinary", &status_candidate(&alice)).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        submit(dir.path(), "urgent-b", &status_candidate(&alice).urgent()).unwrap();

        let pending = list_pending(dir.path(), &alice).unwrap();
        let kinds: Vec<&str> = pending
            .iter()
            .map(|(p, _)| p.file_stem().unwrap().to_str().unwrap())
            .collect();
        assert_eq!(kinds, vec!["urgent-a", "urgent-b", "ordinary"]);
    }
}
