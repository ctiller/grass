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
/// One outbox entry this host could not read as `agent`'s candidate, and
/// why. It is reported and left on disk exactly as found: this host cannot
/// tell the difference between a file some broken writer produced and a
/// well-formed candidate from a *newer* binary than its own, and deleting
/// the second kind loses an event no receipt records.
#[derive(Debug, Clone)]
pub struct UnreadableEntry {
    pub path: PathBuf,
    pub reason: String,
}

/// What `list_pending` found: the candidates it could read, and the entries
/// it could not.
///
/// Two vectors rather than a `Result` because an outbox with one bad file
/// in it is not an unreadable outbox. It used to be: a single entry that
/// failed to deserialize, or that named another agent, returned `Err` for
/// the whole listing, which stopped the coordinator from draining *any* of
/// that agent's queue and stopped `agent-bus outbox` from showing an
/// operator what was in it. That is the same shape as the payload-parse
/// abort in `coordinator::drain_outbox`, one layer earlier and reached
/// first, so fixing only the later one left the outage intact.
#[derive(Debug, Clone, Default)]
pub struct PendingOutbox {
    pub pending: Vec<(PathBuf, Candidate)>,
    pub unreadable: Vec<UnreadableEntry>,
}

pub fn list_pending(git_common_dir: &Path, agent: &Agent) -> AbResult<PendingOutbox> {
    let dir = outbox_dir(git_common_dir, agent);
    if !dir.exists() {
        return Ok(PendingOutbox::default());
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
    let mut unreadable = Vec::new();
    for (path, _) in entries {
        // Every failure below is per-entry. The directory listing above can
        // still fail the call -- an outbox whose directory cannot be read is
        // genuinely unreadable -- but one bad file in it is not.
        let bytes = match std::fs::read(&path) {
            Ok(b) => b,
            Err(e) => {
                unreadable.push(UnreadableEntry {
                    path: path.clone(),
                    reason: format!("could not be read: {e}"),
                });
                continue;
            }
        };
        let candidate: Candidate = match serde_json::from_slice(&bytes) {
            Ok(c) => c,
            Err(e) => {
                unreadable.push(UnreadableEntry {
                    path: path.clone(),
                    reason: format!("is not a readable candidate: {e}"),
                });
                continue;
            }
        };
        if candidate.agent != *agent {
            // Held, not discarded: publishing it here would forge another
            // agent's event, but it is equally not this host's to delete.
            unreadable.push(UnreadableEntry {
                path: path.clone(),
                reason: format!(
                    "claims agent {} but lives under {agent}'s outbox",
                    candidate.agent
                ),
            });
            continue;
        }
        out.push((path, candidate));
    }
    // Stable sort: within the already-established mtime order, urgent
    // candidates move to the front without disturbing relative order among
    // candidates of the same urgency.
    out.sort_by_key(|(_, c)| !c.urgent);
    Ok(PendingOutbox {
        pending: out,
        unreadable,
    })
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

    /// An outbox entry is read back as authoritative for *whose* event it
    /// is, so the directory it sits in and the agent it names must agree.
    /// Nothing else re-checks this: `coordinator::drain_outbox` takes the
    /// deserialized `Candidate` at its word, so a file misfiled into another
    /// agent's outbox would be published as that agent's own event.
    ///
    /// Only reachable by writing the file directly -- `submit` derives the
    /// directory from the candidate, so it cannot produce the mismatch.
    #[test]
    fn list_pending_reports_an_entry_that_names_a_different_agent() {
        let dir = tempfile::tempdir().unwrap();
        let (alice, bob) = (a("alice"), a("bob"));

        // Alice's candidate, filed under Bob's outbox.
        let bob_dir = outbox_dir(dir.path(), &bob);
        std::fs::create_dir_all(&bob_dir).unwrap();
        std::fs::write(
            bob_dir.join("client-1.json"),
            serde_json::to_vec(&status_candidate(&alice)).unwrap(),
        )
        .unwrap();

        // Reported as unreadable, not returned as an error for the whole
        // listing: it is not Bob's to publish, and equally not Bob's to
        // delete. A `return Err` here used to stop every one of Bob's own
        // candidates from being drained because someone else's file was
        // sitting in his directory.
        let listing = list_pending(dir.path(), &bob).unwrap();
        assert!(listing.pending.is_empty());
        assert_eq!(listing.unreadable.len(), 1);
        assert!(
            listing.unreadable[0].reason.contains("claims agent alice"),
            "the reason must name the claimed agent: {}",
            listing.unreadable[0].reason
        );
        // Still on disk, untouched.
        assert!(bob_dir.join("client-1.json").exists());
    }

    /// One unreadable file does not hide the readable candidates beside it.
    ///
    /// This is the outage `coordinator::drain_outbox` was fixed for, one
    /// layer earlier: `list_pending` runs before the drain loop, so while it
    /// answered a single bad file with `Err` the per-candidate rejection
    /// below it could never be reached at all.
    #[test]
    fn list_pending_reports_an_unreadable_entry_without_hiding_the_rest() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        std::fs::write(
            outbox_dir(dir.path(), &alice).join("client-2.json"),
            b"{ this is not a candidate",
        )
        .unwrap();
        submit(dir.path(), "client-3", &status_candidate(&alice)).unwrap();

        let listing = list_pending(dir.path(), &alice).unwrap();
        assert_eq!(
            listing.pending.len(),
            2,
            "both readable candidates must survive a bad file between them"
        );
        assert_eq!(listing.unreadable.len(), 1);
        assert!(listing.unreadable[0]
            .reason
            .contains("is not a readable candidate"));
        assert!(listing.unreadable[0].path.ends_with("client-2.json"));
    }

    #[test]
    fn submit_then_list_pending_round_trips() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        let pending = list_pending(dir.path(), &alice).unwrap().pending;
        assert_eq!(pending.len(), 1);
        assert_eq!(pending[0].1, status_candidate(&alice));
    }

    #[test]
    fn list_pending_is_empty_before_any_submission() {
        let dir = tempfile::tempdir().unwrap();
        assert!(list_pending(dir.path(), &a("alice"))
            .unwrap()
            .pending
            .is_empty());
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
        assert_eq!(list_pending(dir.path(), &alice).unwrap().pending.len(), 1);
    }

    #[test]
    fn two_client_ids_from_the_same_agent_both_persist() {
        let dir = tempfile::tempdir().unwrap();
        let alice = a("alice");
        submit(dir.path(), "client-1", &status_candidate(&alice)).unwrap();
        submit(dir.path(), "client-2", &status_candidate(&alice)).unwrap();
        assert_eq!(list_pending(dir.path(), &alice).unwrap().pending.len(), 2);
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
        let pending = list_pending(dir.path(), &alice).unwrap().pending;
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
        assert!(list_pending(dir.path(), &alice).unwrap().pending.is_empty());
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

        let pending = list_pending(dir.path(), &alice).unwrap().pending;
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

        let pending = list_pending(dir.path(), &alice).unwrap().pending;
        let kinds: Vec<&str> = pending
            .iter()
            .map(|(p, _)| p.file_stem().unwrap().to_str().unwrap())
            .collect();
        assert_eq!(kinds, vec!["urgent-a", "urgent-b", "ordinary"]);
    }
}
