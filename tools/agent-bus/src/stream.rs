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
use crate::error::{invalid, AbResult};
use crate::gitobjects::{ObjectReader, ObjectWriter, RefStore};
use crate::scalars::{Agent, Branch, EventId, ObjectId};
use serde::{Deserialize, Serialize};
use std::path::Path;

pub const STREAM_REF_PREFIX: &str = "refs/heads/agent-events/";

/// The agent grammar (`[a-z][a-z0-9-]{0,47}`) is already a valid single ref
/// component, so this can never fail `Branch::parse`.
pub fn stream_ref(agent: &Agent) -> Branch {
    Branch::parse(format!("{STREAM_REF_PREFIX}{agent}"))
        .expect("agent name is a valid ref component")
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StreamHeader {
    pub agent: Agent,
    /// The version-one bus event that activated version two, for an
    /// identity migrated from an existing v1 fleet. `None` for a stream
    /// created directly under a v2-native genesis with no v1 history to
    /// activate from (e.g. a fresh deployment, or this crate's own tests).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub activation_event: Option<EventId>,
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
    crate::gitobjects::Libgit2Reader::open(repo)?.resolve(stream_ref(agent).as_str())
}

fn read_header_at(
    reader: &dyn crate::gitobjects::ObjectReader,
    tip: &ObjectId,
) -> AbResult<StreamHeader> {
    let bytes = reader.read_blob_at(tip, HEADER_FILE)?.ok_or_else(|| {
        invalid(format!(
            "stream commit {tip} has no {HEADER_FILE}; it is not a stream commit"
        ))
    })?;
    StreamHeader::parse(&bytes)
}

/// Reads and structurally validates the full stream for `agent`: the header
/// plus every event, in order. Does not itself check frontier completeness,
/// registry membership, or custody -- see `frontier.rs`/`registry.rs` for
/// that, applied by the caller once it has the registry epoch this stream's
/// events claim to observe.
///
/// Reads the blobs straight out of the object database (`gitobjects.rs`),
/// so no worktree is materialized -- and therefore no scratch directory to
/// check one out into is needed or accepted any more.
pub fn read_stream(repo: &Path, agent: &Agent) -> AbResult<(StreamHeader, Vec<Envelope>)> {
    let tip = read_stream_tip(repo, agent)?.ok_or_else(|| {
        invalid(format!(
            "{agent} has no stream -- either it was never registered, or it is registered but \
             has not yet published its first event; if newly registered, run `coordinate` for \
             it first"
        ))
    })?;
    let reader = crate::gitobjects::Libgit2Reader::open(repo)?;
    read_stream_at(&reader, &tip, agent)
}

/// [`read_stream`] against an already-resolved tip and an already-open
/// reader. Callers reading many streams in one pass (`sync::reduce_local`,
/// `coordinator::build_complete_frontier`) open one reader and loop over
/// this rather than paying a repository open per stream.
pub fn read_stream_at(
    reader: &dyn crate::gitobjects::ObjectReader,
    tip: &ObjectId,
    agent: &Agent,
) -> AbResult<(StreamHeader, Vec<Envelope>)> {
    let header = read_header_at(reader, tip)?;
    if header.agent != *agent {
        return Err(invalid(format!(
            "{agent}'s stream header names agent {}",
            header.agent
        )));
    }
    let log = crate::storage::read_stream_log_at(reader, tip, agent)?;
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
    if first_event.agent != header.agent {
        return Err(invalid(format!(
            "the root event belongs to {} but the header describes {}'s stream",
            first_event.agent, header.agent
        )));
    }

    // Test-only seam: a competing writer lands here, after the existence
    // check above and before the root commit is built.
    #[cfg(test)]
    crate::gitobjects::fire_competing_writer();

    let git = crate::gitobjects::Libgit2Reader::open(repo)?;

    // Segments are strict LF-only (`storage.rs`'s structural checks reject a
    // CR byte outright). Nothing in this crate checks a stream out any more,
    // so no `core.autocrlf` rewrite can reach the content on our own read
    // path -- but a person or another tool inspecting a stream with an
    // ordinary `git checkout` still can, and this file is already part of
    // every stream tree published so far. Keeping it costs one blob and
    // keeps new streams byte-comparable with existing ones.
    let attributes = git.write_blob(b"*.jsonl -text\nheader.json -text\n")?;
    let header_blob = git.write_blob(&header.to_canonical_bytes())?;
    let segment_name = crate::storage::segment_filename(0);
    let segment_blob = git.write_blob(&segment_bytes(
        std::slice::from_ref(first_event),
        Vec::new(),
    )?)?;

    let tree = git.write_tree(
        None,
        &[
            (".gitattributes", attributes),
            (HEADER_FILE, header_blob),
            (segment_name.as_str(), segment_blob),
        ],
    )?;
    let commit = git.create_commit(
        &tree,
        &[],
        &format!("agent-events: {} stream root", header.agent),
    )?;

    // `expected = None` means "only if this ref does not exist". The check
    // at the top of this function read the tip a moment ago; this is what
    // makes a second writer that registered the same agent in that window
    // lose rather than silently overwrite the winner's root.
    git.compare_and_set(stream_ref(&header.agent).as_str(), None, &commit)?;
    Ok(commit)
}

/// The bytes of a segment file holding `existing` followed by `events`.
///
/// Split out because both the root commit (which starts from nothing) and an
/// append (which starts from the parent commit's segment blob) need it, and
/// because it is where the per-line size bound is enforced.
fn segment_bytes(events: &[Envelope], existing: Vec<u8>) -> AbResult<Vec<u8>> {
    let mut out = existing;
    for env in events {
        let line = env.to_canonical_line();
        if line.len() > crate::storage::MAX_LINE_BYTES {
            return Err(invalid(format!(
                "event line exceeds {} bytes",
                crate::storage::MAX_LINE_BYTES
            )));
        }
        out.extend_from_slice(line.as_bytes());
        out.push(b'\n');
    }
    Ok(out)
}

/// The segment-file contents `new_events` imply, given `base`'s tree as the
/// starting point.
///
/// Mirrors what `storage::append_event` enforced when it was writing real
/// files one at a time: an event at offset zero must start a segment that
/// does not exist yet, and an event at a non-zero offset must continue one
/// that does. The difference is that those were `path.exists()` questions
/// about a checked-out directory, and these are questions about `base`'s
/// tree -- so a stale or half-written worktree cannot answer them wrongly.
fn segment_edits(
    reader: &impl ObjectReader,
    base: &ObjectId,
    agent: &Agent,
    new_events: &[Envelope],
) -> AbResult<Vec<(String, Vec<u8>)>> {
    let mut edits: std::collections::BTreeMap<String, Vec<u8>> = std::collections::BTreeMap::new();
    for env in new_events {
        let segment = crate::storage::segment_index(env.seq);
        let offset = crate::storage::segment_offset(env.seq);
        let name = crate::storage::segment_filename(segment);

        if !edits.contains_key(&name) {
            let existing = reader.read_blob_at(base, &name)?;
            let start = match (offset, existing) {
                (0, None) => Vec::new(),
                (0, Some(_)) => {
                    return Err(invalid(format!(
                        "segment {segment} for {agent} already exists but a fresh segment was \
                         expected"
                    )))
                }
                (_, Some(bytes)) => bytes,
                (_, None) => {
                    return Err(invalid(format!(
                        "expected existing segment {segment} for {agent} at offset {offset}"
                    )))
                }
            };
            edits.insert(name.clone(), start);
        }

        let buf = edits
            .get_mut(&name)
            .expect("the segment was just inserted above");
        *buf = segment_bytes(std::slice::from_ref(env), std::mem::take(buf))?;
    }
    Ok(edits.into_iter().collect())
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

    // Test-only seam: a competing writer lands here, after the staleness
    // check above and before this append's commit is built. Gate 6 says the
    // loser stops; this is where a test makes this call the loser.
    #[cfg(test)]
    crate::gitobjects::fire_competing_writer();

    let git = crate::gitobjects::Libgit2Reader::open(repo)?;

    // Three properties the previous implementation checked *after* building
    // a commit -- "the header did not change", "no unexpected path was
    // touched", "there is exactly one parent, and it is `expected_parent`"
    // -- are structural here. This edits only the segment names
    // `segment_edits` derives from the events' own sequence numbers, carries
    // every other entry of the parent tree through untouched, and names
    // exactly one parent. There is nothing left to re-check, and no way for
    // a dirty or stale working tree to introduce a fourth path.
    let mut edits = Vec::new();
    for (name, bytes) in segment_edits(&git, expected_parent, agent, new_events)? {
        edits.push((name, git.write_blob(&bytes)?));
    }
    let tree = git.write_tree(
        Some(expected_parent),
        &edits
            .iter()
            .map(|(name, blob)| (name.as_str(), blob.clone()))
            .collect::<Vec<_>>(),
    )?;
    let commit = git.create_commit(
        &tree,
        &[expected_parent],
        &format!(
            "agent-events: {agent} +{} event(s) through {}",
            new_events.len(),
            new_events.last().unwrap().id
        ),
    )?;

    // The staleness check at the top of this function read the tip before
    // any of the above ran, and building a commit takes real time. Naming
    // `expected_parent` here closes that window: a writer that landed in it
    // wins, and this one is told to resolve custody rather than overwriting
    // the winner.
    git.compare_and_set(stream_ref(agent).as_str(), Some(expected_parent), &commit)?;
    Ok(commit)
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
            activation_event: Some(EventId::new(&a("coord1"), 0)),
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

    // ---------------------------------------------- segment construction
    //
    // These are the rules `storage::append_event` used to enforce against a
    // checked-out directory, now enforced against the parent commit's tree.
    // Each is stated as a falsification: the violating input, and the
    // specific rejection it must produce.

    fn seg0() -> String {
        crate::storage::segment_filename(0)
    }

    #[test]
    fn segment_edits_starts_a_fresh_segment_at_offset_zero() {
        let alice = a("alice");
        let base = hash(7);
        let reader = crate::gitobjects::FixtureObjectReader::new().with_blob(
            &base,
            HEADER_FILE,
            header(&alice).to_canonical_bytes(),
        );
        let env = registered_envelope(&alice, 0);
        let edits = segment_edits(&reader, &base, &alice, std::slice::from_ref(&env)).unwrap();
        assert_eq!(edits.len(), 1);
        assert_eq!(edits[0].0, seg0());
        assert_eq!(
            String::from_utf8(edits[0].1.clone()).unwrap(),
            format!(
                "{}
",
                env.to_canonical_line()
            )
        );
    }

    #[test]
    fn segment_edits_appends_after_the_existing_content() {
        let alice = a("alice");
        let base = hash(7);
        let first = registered_envelope(&alice, 0);
        let reader = crate::gitobjects::FixtureObjectReader::new().with_blob(
            &base,
            &seg0(),
            format!(
                "{}
",
                first.to_canonical_line()
            ),
        );
        let second = status_envelope(&alice, 1);
        let edits = segment_edits(&reader, &base, &alice, std::slice::from_ref(&second)).unwrap();
        let body = String::from_utf8(edits[0].1.clone()).unwrap();
        assert_eq!(body.lines().count(), 2, "must keep the existing line");
        assert!(body.ends_with(&format!(
            "{}
",
            second.to_canonical_line()
        )));
    }

    /// Falsification: an event at a non-zero offset whose segment does not
    /// exist in the parent tree means the stream is not contiguous.
    #[test]
    fn segment_edits_rejects_an_offset_with_no_existing_segment() {
        let alice = a("alice");
        let base = hash(7);
        let reader = crate::gitobjects::FixtureObjectReader::new().with_blob(
            &base,
            HEADER_FILE,
            header(&alice).to_canonical_bytes(),
        );
        let env = status_envelope(&alice, 1);
        let err = segment_edits(&reader, &base, &alice, std::slice::from_ref(&env)).unwrap_err();
        assert!(
            err.to_string().contains("expected existing segment"),
            "{err}"
        );
    }

    /// Falsification: an event at offset zero whose segment already exists
    /// would silently overwrite published events.
    #[test]
    fn segment_edits_rejects_a_fresh_segment_that_already_exists() {
        let alice = a("alice");
        let base = hash(7);
        let reader = crate::gitobjects::FixtureObjectReader::new().with_blob(
            &base,
            &seg0(),
            "{}
",
        );
        let env = registered_envelope(&alice, 0);
        let err = segment_edits(&reader, &base, &alice, std::slice::from_ref(&env)).unwrap_err();
        assert!(
            err.to_string()
                .contains("already exists but a fresh segment was expected"),
            "{err}"
        );
    }

    /// The size bound is inclusive at its limit: a line of exactly
    /// `MAX_LINE_BYTES` is accepted, one byte more is not.
    ///
    /// Both halves are needed. `segment_bytes_rejects_an_oversized_line`
    /// alone uses `MAX_LINE_BYTES + 10`, so mutating the comparison from `>`
    /// to `>=` -- rejecting a line that is exactly at the limit -- left the
    /// suite green.
    #[test]
    fn segment_bytes_accepts_a_line_of_exactly_the_maximum() {
        let alice = a("alice");
        let mut env = registered_envelope(&alice, 0);
        // Converge on a payload whose *encoded line* is exactly at the bound.
        // Setting `data` changes the envelope's length, so the padding cannot
        // be computed in one step from the original.
        let mut pad = crate::storage::MAX_LINE_BYTES;
        for _ in 0..8 {
            env.data = serde_json::json!({ "blob": "x".repeat(pad) });
            let len = env.to_canonical_line().len();
            if len == crate::storage::MAX_LINE_BYTES {
                break;
            }
            pad = (pad + crate::storage::MAX_LINE_BYTES).saturating_sub(len);
        }
        let line = env.to_canonical_line();
        assert_eq!(
            line.len(),
            crate::storage::MAX_LINE_BYTES,
            "fixture must sit exactly on the bound, not near it"
        );
        assert!(segment_bytes(std::slice::from_ref(&env), Vec::new()).is_ok());

        // One byte over is refused.
        env.data = serde_json::json!({ "blob": "x".repeat(pad + 1) });
        let err = segment_bytes(std::slice::from_ref(&env), Vec::new()).unwrap_err();
        assert!(err.to_string().contains("event line exceeds"), "{err}");
    }

    /// Falsification: the per-line size bound `storage::MAX_LINE_BYTES` sets.
    #[test]
    fn segment_bytes_rejects_an_oversized_line() {
        let alice = a("alice");
        let mut env = registered_envelope(&alice, 0);
        env.data = serde_json::json!({
            "blob": "x".repeat(crate::storage::MAX_LINE_BYTES + 10)
        });
        let err = segment_bytes(std::slice::from_ref(&env), Vec::new()).unwrap_err();
        assert!(err.to_string().contains("event line exceeds"), "{err}");
    }

    /// A batch that crosses the segment boundary must open the next segment
    /// rather than growing the current one past `SEGMENT_SIZE`.
    #[test]
    fn segment_edits_rolls_over_to_the_next_segment() {
        let alice = a("alice");
        let base = hash(7);
        let last = crate::storage::SEGMENT_SIZE - 1;
        let existing: String = (0..last)
            .map(|i| {
                format!(
                    "{}
",
                    status_envelope(&alice, i).to_canonical_line()
                )
            })
            .collect();
        let reader =
            crate::gitobjects::FixtureObjectReader::new().with_blob(&base, &seg0(), existing);
        let batch = [
            status_envelope(&alice, last),
            status_envelope(&alice, crate::storage::SEGMENT_SIZE),
        ];
        let edits = segment_edits(&reader, &base, &alice, &batch).unwrap();
        let names: Vec<&str> = edits.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(
            names,
            vec![seg0(), crate::storage::segment_filename(1)],
            "the boundary-crossing event must open segment 1"
        );
        let rolled = String::from_utf8(edits[1].1.clone()).unwrap();
        assert_eq!(rolled.lines().count(), 1);
    }

    // ------------------------------------------- the compare-and-swap itself
    //
    // Every test below lands a competing writer *inside* the window between
    // the caller's staleness pre-check and the ref update. Without that,
    // mutation testing showed the CAS could be defeated at this call site --
    // passing the ref's current tip as `expected`, or dropping the expected
    // value entirely -- with the whole suite still green, because the
    // pre-check alone produced an error whose wording the tests could not
    // distinguish from the CAS's.

    /// Publish an unrelated commit on `refname`, as another writer would.
    fn land_competing_writer(repo: &std::path::Path, refname: &str) {
        let g = crate::gitobjects::Libgit2Reader::open(repo).unwrap();
        let blob = g.write_blob(b"a competing writer's content").unwrap();
        let tree = g.write_tree(None, &[("competing.txt", blob)]).unwrap();
        let commit = g.create_commit(&tree, &[], "competing writer").unwrap();
        // Through `git`, not `compare_and_set`, so this does not re-enter the
        // seam it is being fired from.
        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(repo)
            .args(["update-ref", refname, commit.as_str()])
            .status()
            .unwrap();
        assert!(status.success(), "the competing writer could not publish");
    }

    /// Gate 6's real teeth. The staleness check at the top of
    /// `append_to_stream` reads the tip before any commit is built; a writer
    /// that lands while the commit is being built passes that check and must
    /// still be refused.
    #[test]
    fn append_to_stream_refuses_a_writer_that_lands_after_the_staleness_check() {
        let repo = init_repo();
        let alice = a("alice");
        create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();
        let root = read_stream_tip(repo.path(), &alice).unwrap().unwrap();

        let path = repo.path().to_path_buf();
        let refname = stream_ref(&alice).into_string();
        let _armed = crate::gitobjects::arm_competing_writer(move || {
            land_competing_writer(&path, &refname);
        });

        let err = append_to_stream(repo.path(), &alice, &root, &[status_envelope(&alice, 1)])
            .unwrap_err();
        assert!(
            err.to_string()
                .contains("changed after this write was prepared"),
            "expected the compare-and-swap to refuse, got: {err}"
        );
    }

    /// The same window for a stream root, where the expected value is "this
    /// ref must not exist" rather than a commit id.
    #[test]
    fn create_root_commit_refuses_a_root_that_lands_after_the_existence_check() {
        let repo = init_repo();
        let alice = a("alice");

        let path = repo.path().to_path_buf();
        let refname = stream_ref(&alice).into_string();
        let _armed = crate::gitobjects::arm_competing_writer(move || {
            land_competing_writer(&path, &refname);
        });

        let err = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("already exists"),
            "expected create-if-absent to refuse, got: {err}"
        );
    }

    /// Falsification of the header guard added with the in-process writer: a
    /// root event belonging to a different agent than the header describes.
    #[test]
    fn create_root_commit_rejects_a_root_event_from_another_agent() {
        let repo = init_repo();
        let alice = a("alice");
        let bob = a("bob");
        let err = create_root_commit(repo.path(), &header(&alice), &registered_envelope(&bob, 0))
            .unwrap_err();
        assert!(
            err.to_string().contains("but the header describes"),
            "{err}"
        );
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
        let commit = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();
        assert_eq!(
            read_stream_tip(repo.path(), &alice).unwrap(),
            Some(commit.clone())
        );

        let (read_header, log) = read_stream(repo.path(), &alice).unwrap();
        assert_eq!(read_header, header(&alice));
        assert_eq!(log.len(), 1);
        assert_eq!(log[0].kind, "agent.registered");
    }

    /// Regression test for a Critical, previously-invisible finding: an
    /// earlier version of this function used `git branch -f
    /// <fully-qualified-name> <commit>`, which does not treat a name
    /// starting with `refs/heads/` as the ref itself -- it silently
    /// creates a literal, double-prefixed `refs/heads/refs/heads/
    /// agent-events/<agent>` (confirmed empirically against the pinned git
    /// version). `rev-parse`'s own ref-disambiguation fallback happened to
    /// also resolve that malformed name whenever nothing correctly-named
    /// existed yet, which is exactly why every purely-local round trip
    /// (like the test directly above) passed regardless: reads and writes
    /// were *consistently* wrong in the same way. The moment anything else
    /// creates the correctly-named ref (a real `git fetch`, e.g. gate 17's
    /// currency probe, or another agent's `--sync`), `rev-parse`'s exact
    /// match takes priority over that fallback, and every local commit
    /// made through the malformed name becomes permanently invisible --
    /// silently publishing stale content on the next push. This checks the
    /// *actual* ref set (`for-each-ref`, not `rev-parse`, which is exactly
    /// what would paper over the bug) names precisely
    /// `refs/heads/agent-events/<agent>`, with nothing else present.
    #[test]
    fn create_root_commit_writes_exactly_the_correctly_named_ref() {
        let repo = init_repo();
        let alice = a("alice");
        create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();

        // The *actual* ref set, not `rev-parse` -- which is exactly what
        // would paper over the bug this guards.
        let all = crate::gitobjects::Libgit2Reader::open(repo.path())
            .unwrap()
            .list("refs/")
            .unwrap();
        let refs: Vec<&str> = all.iter().map(|(name, _)| name.as_str()).collect();
        assert!(
            refs.contains(&"refs/heads/agent-events/alice"),
            "expected refs/heads/agent-events/alice among {refs:?}"
        );
        assert!(
            !refs.iter().any(|r| r.contains("refs/heads/refs/heads")),
            "must never create a double-prefixed ref: {refs:?}"
        );
    }

    /// Companion regression test proving the actual failure mode the bug
    /// above caused: once a *correctly-named* ref for this agent also
    /// exists (simulating a fetch that landed an older value, exactly as a
    /// concurrent `--sync` elsewhere would), a *later* local write here
    /// must still be the one `read_stream_tip` reports -- not silently
    /// shadowed by the earlier, now-stale fetched value.
    #[test]
    fn append_to_stream_is_not_shadowed_by_a_stale_same_named_ref_from_elsewhere() {
        let repo = init_repo();
        let alice = a("alice");
        let root = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();

        // Simulate a concurrent fetch elsewhere landing the *same* (still
        // correctly-named, by definition of a real fetch) ref at the
        // *old* value -- a no-op here since it's already there, but
        // establishes that the ref genuinely is the plain, correctly
        // -named one before the real assertion below.
        crate::gitrepo::run_ok(
            repo.path(),
            &["update-ref", "refs/heads/agent-events/alice", root.as_str()],
        )
        .unwrap();

        let advanced =
            append_to_stream(repo.path(), &alice, &root, &[status_envelope(&alice, 1)]).unwrap();

        assert_eq!(
            read_stream_tip(repo.path(), &alice).unwrap(),
            Some(advanced),
            "the later local write must be visible, not shadowed by the earlier value"
        );
    }

    #[test]
    fn create_root_commit_rejects_a_second_root() {
        let repo = init_repo();
        let alice = a("alice");
        create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();
        let err = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap_err();
        assert!(err.to_string().contains("already exists"), "{err}");
    }

    #[test]
    fn create_root_commit_rejects_a_first_event_that_is_not_agent_registered() {
        let repo = init_repo();
        let alice = a("alice");
        let err = create_root_commit(repo.path(), &header(&alice), &status_envelope(&alice, 0))
            .unwrap_err();
        assert!(err.to_string().contains("agent.registered"), "{err}");
    }

    #[test]
    fn append_to_stream_extends_with_exactly_one_new_commit() {
        let repo = init_repo();
        let alice = a("alice");
        let root = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();

        let new_tip =
            append_to_stream(repo.path(), &alice, &root, &[status_envelope(&alice, 1)]).unwrap();
        assert_eq!(
            read_stream_tip(repo.path(), &alice).unwrap(),
            Some(new_tip.clone())
        );
        assert_eq!(
            crate::gitrepo::parents_of(repo.path(), new_tip.as_str()).unwrap(),
            vec![root.as_str().to_string()]
        );

        let (_h, log) = read_stream(repo.path(), &alice).unwrap();
        assert_eq!(log.len(), 2);
        assert_eq!(log[1].seq, 1);
    }

    /// Gate 6's local half: a stale `expected_parent` (the stream moved
    /// since it was read) must be refused, not silently rebased through.
    #[test]
    fn append_to_stream_rejects_a_stale_expected_parent() {
        let repo = init_repo();
        let alice = a("alice");
        let root = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();
        // Advance the stream out from under a caller still holding `root`.
        append_to_stream(repo.path(), &alice, &root, &[status_envelope(&alice, 1)]).unwrap();

        let err = append_to_stream(
            repo.path(),
            &alice,
            &root, // stale: the real tip has already advanced past this
            &[status_envelope(&alice, 1)],
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("stale or duplicate custody"),
            "{err}"
        );
    }

    #[test]
    fn append_to_stream_rejects_an_event_belonging_to_a_different_agent() {
        let repo = init_repo();
        let alice = a("alice");
        let bob = a("bob");
        let root = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();
        let err =
            append_to_stream(repo.path(), &alice, &root, &[status_envelope(&bob, 1)]).unwrap_err();
        assert!(err.to_string().contains("does not belong to"), "{err}");
    }

    #[test]
    fn append_to_stream_rejects_an_empty_batch() {
        let repo = init_repo();
        let alice = a("alice");
        let root = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();
        let err = append_to_stream(repo.path(), &alice, &root, &[]).unwrap_err();
        assert!(err.to_string().contains("at least one event"), "{err}");
    }

    #[test]
    fn read_stream_fails_for_an_agent_with_no_stream() {
        let repo = init_repo();
        let err = read_stream(repo.path(), &a("nobody")).unwrap_err();
        assert!(err.to_string().contains("has no stream"), "{err}");
    }

    // ------------------------------------ reading a stream out of history
    //
    // `read_stream_at`'s own branches, driven by a `FixtureObjectReader` so
    // each malformed shape can be stated directly. Building these through
    // the real write path is not possible -- `create_root_commit` refuses
    // most of them -- which is exactly why the trait has a test
    // implementation.

    fn tip() -> ObjectId {
        ObjectId::parse("ab".repeat(20)).unwrap()
    }

    fn stream_blobs(agent: &Agent) -> crate::gitobjects::FixtureObjectReader {
        crate::gitobjects::FixtureObjectReader::new()
            .with_blob(&tip(), HEADER_FILE, header(agent).to_canonical_bytes())
            .with_blob(
                &tip(),
                "000000.jsonl",
                format!("{}\n", registered_envelope(agent, 0).to_canonical_line()),
            )
    }

    #[test]
    fn read_stream_at_reads_a_well_formed_stream() {
        let alice = a("alice");
        let (h, log) = read_stream_at(&stream_blobs(&alice), &tip(), &alice).unwrap();
        assert_eq!(h, header(&alice));
        assert_eq!(log.len(), 1);
    }

    /// A commit with no `header.json` is not a stream commit at all. It must
    /// say so, rather than surfacing a bare "missing file" that gives the
    /// reader nothing to act on.
    #[test]
    fn read_stream_at_rejects_a_commit_with_no_header() {
        let alice = a("alice");
        let r = crate::gitobjects::FixtureObjectReader::new().with_blob(
            &tip(),
            "000000.jsonl",
            format!("{}\n", registered_envelope(&alice, 0).to_canonical_line()),
        );
        let err = read_stream_at(&r, &tip(), &alice).unwrap_err();
        assert!(err.to_string().contains("is not a stream commit"), "{err}");
        assert!(err.to_string().contains(tip().as_str()), "{err}");
    }

    #[test]
    fn read_stream_at_rejects_a_malformed_header() {
        let alice = a("alice");
        let r = stream_blobs(&alice).with_blob(&tip(), HEADER_FILE, b"not json");
        let err = read_stream_at(&r, &tip(), &alice).unwrap_err();
        assert!(err.to_string().contains("malformed stream header"), "{err}");
    }

    /// Reading agent A's ref must not silently accept a tree holding agent
    /// B's header -- the header is the stream's own claim of ownership.
    #[test]
    fn read_stream_at_rejects_a_header_naming_a_different_agent() {
        let alice = a("alice");
        let bob = a("bob");
        let r =
            stream_blobs(&alice).with_blob(&tip(), HEADER_FILE, header(&bob).to_canonical_bytes());
        let err = read_stream_at(&r, &tip(), &alice).unwrap_err();
        assert!(err.to_string().contains("header names agent bob"), "{err}");
    }

    #[test]
    fn read_stream_at_rejects_a_stream_with_no_segments() {
        let alice = a("alice");
        let r = crate::gitobjects::FixtureObjectReader::new().with_blob(
            &tip(),
            HEADER_FILE,
            header(&alice).to_canonical_bytes(),
        );
        let err = read_stream_at(&r, &tip(), &alice).unwrap_err();
        assert!(err.to_string().contains("has no segments"), "{err}");
    }

    #[test]
    fn read_stream_at_propagates_an_unresolvable_commit() {
        let alice = a("alice");
        let other = ObjectId::parse("cd".repeat(20)).unwrap();
        let err = read_stream_at(&stream_blobs(&alice), &other, &alice).unwrap_err();
        assert!(matches!(err, crate::error::AbError::Git(_)), "got {err:?}");
    }

    /// The end-to-end proof that matters: real commits made by the crate's
    /// own real write path, spanning a segment rollover, read back through
    /// libgit2 with no worktree materialized. `append_to_stream` rolls over
    /// at `SEGMENT_SIZE`, so 1001 events means segment `000000.jsonl` closed
    /// at exactly 1000 plus a `000001.jsonl` tail -- the multi-segment shape
    /// the old worktree reader used to see as two files on disk.
    #[test]
    fn read_stream_reads_a_real_multi_segment_stream_across_a_rollover() {
        let repo = init_repo();
        let alice = a("alice");
        let root = create_root_commit(
            repo.path(),
            &header(&alice),
            &registered_envelope(&alice, 0),
        )
        .unwrap();

        let rest: Vec<Envelope> = (1..=crate::storage::SEGMENT_SIZE)
            .map(|seq| status_envelope(&alice, seq))
            .collect();
        append_to_stream(repo.path(), &alice, &root, &rest).unwrap();

        let (read_header, log) = read_stream(repo.path(), &alice).unwrap();
        assert_eq!(read_header, header(&alice));
        assert_eq!(log.len() as u64, crate::storage::SEGMENT_SIZE + 1);
        assert_eq!(log[0].kind, "agent.registered");
        assert_eq!(log[1000].seq, 1000);
        // Every event, in order, with no gap across the segment boundary.
        for (i, env) in log.iter().enumerate() {
            assert_eq!(env.seq, i as u64);
            assert_eq!(env.agent, alice);
        }

        // ...and the read genuinely materialized nothing: the only
        // directories under the repo are the two the write path made.
        let stray: Vec<String> = std::fs::read_dir(repo.path())
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .filter(|n| n.starts_with("stream-read-") || n.starts_with("_reads"))
            .collect();
        assert!(stray.is_empty(), "read materialized worktrees: {stray:?}");
    }
}
