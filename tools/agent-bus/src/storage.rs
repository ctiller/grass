//! Segmented JSONL storage within one agent's own stream tree
//! (docs/AGENT_COORDINATION_EVOLUTION.md section 2.1).
//!
//! Version one laid segments out under `<bus_root>/<agent>/NNNNNN.jsonl`
//! because one shared tree held every agent's directory side by side.
//! Version two gives each agent its own git ref (`refs/heads/agent-events/
//! <agent>`, see `stream.rs`), so a stream's own working tree already
//! belongs to exactly one agent -- segments live directly at that tree's
//! root as `NNNNNN.jsonl`, with no per-agent subdirectory needed. Every
//! byte-level validation rule (segment size, no CR/BOM, contiguous
//! sequence, no partial final line) is otherwise unchanged from version
//! one, since none of it depended on the multi-agent tree shape.

use crate::envelope::Envelope;
use crate::error::{invalid, AbResult};
use crate::scalars::Agent;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

pub const SEGMENT_SIZE: u64 = 1000;
pub const MAX_LINE_BYTES: usize = 65_536;

pub fn segment_index(seq: u64) -> u64 {
    seq / SEGMENT_SIZE
}

pub fn segment_offset(seq: u64) -> u64 {
    seq % SEGMENT_SIZE
}

pub fn segment_filename(segment: u64) -> String {
    format!("{segment:06}.jsonl")
}

pub fn segment_path(stream_root: &Path, segment: u64) -> PathBuf {
    stream_root.join(segment_filename(segment))
}

/// Raw, purely-structural read of one segment file: UTF-8, LF-only,
/// no BOM/CR, no blank lines, no partial final line, per-line byte cap.
pub fn read_segment_lines(path: &Path) -> AbResult<Vec<String>> {
    let bytes = fs::read(path).map_err(|e| crate::error::AbError::Io {
        path: path.display().to_string(),
        source: e,
    })?;
    read_segment_lines_from_bytes(&path.display().to_string(), &bytes)
}

/// Same structural checks as [`read_segment_lines`], but over an in-memory
/// byte slice (used both for files on disk and for blobs read out of Git
/// history). `label` is used only for error messages.
pub fn read_segment_lines_from_bytes(label: &str, bytes: &[u8]) -> AbResult<Vec<String>> {
    if bytes.is_empty() {
        return Err(invalid(format!("empty segment content: {label}")));
    }
    if bytes.starts_with(&[0xEF, 0xBB, 0xBF]) {
        return Err(invalid(format!("byte-order mark in {label}")));
    }
    if bytes.contains(&b'\r') {
        return Err(invalid(format!("CR byte in {label}")));
    }
    let text =
        std::str::from_utf8(bytes).map_err(|e| invalid(format!("{label} not UTF-8: {e}")))?;
    if !text.ends_with('\n') {
        return Err(invalid(format!(
            "{label} has a partial final line (missing trailing LF)"
        )));
    }
    let body = &text[..text.len() - 1];
    if body.is_empty() {
        return Err(invalid(format!("empty segment content: {label}")));
    }
    let mut lines = Vec::new();
    for line in body.split('\n') {
        if line.is_empty() {
            return Err(invalid(format!("blank line in {label}")));
        }
        if line.len() > MAX_LINE_BYTES {
            return Err(invalid(format!(
                "line exceeds {MAX_LINE_BYTES} bytes in {label}"
            )));
        }
        lines.push(line.to_string());
    }
    Ok(lines)
}

#[derive(Debug)]
pub struct StreamSegmentFile {
    pub segment: u64,
    pub lines: Vec<String>,
}

/// Discover and structurally read every segment in one stream's working
/// tree, enforcing contiguous zero-based segment numbers, closed non-tail
/// segments with exactly `SEGMENT_SIZE` events, and a non-empty,
/// non-overflowing tail. `stream_root` is a real checked-out worktree (see
/// `stream.rs`), so `.git` (the worktree's admin link) and `.gitattributes`
/// (the stream root's `-text` pin for its own segment files) are present
/// alongside the header and segments and must be ignored rather than
/// rejected.
pub fn read_stream_segments(stream_root: &Path) -> AbResult<Vec<StreamSegmentFile>> {
    let mut segments: std::collections::BTreeMap<u64, PathBuf> = std::collections::BTreeMap::new();
    for entry in fs::read_dir(stream_root).map_err(|e| crate::error::AbError::Io {
        path: stream_root.display().to_string(),
        source: e,
    })? {
        let entry = entry.map_err(|e| crate::error::AbError::Io {
            path: stream_root.display().to_string(),
            source: e,
        })?;
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name == "header.json" || name == ".git" || name == ".gitattributes" {
            continue;
        }
        if !name.ends_with(".jsonl") {
            return Err(invalid(format!(
                "unexpected file in stream tree: {}",
                path.display()
            )));
        }
        let stem = &name[..name.len() - ".jsonl".len()];
        if stem.len() != 6 || !stem.chars().all(|c| c.is_ascii_digit()) {
            return Err(invalid(format!(
                "malformed segment filename: {}",
                path.display()
            )));
        }
        let segment: u64 = stem
            .parse()
            .map_err(|_| invalid(format!("malformed segment number: {name}")))?;
        segments.insert(segment, path);
    }
    if segments.is_empty() {
        return Err(invalid(format!(
            "stream tree has no segments: {}",
            stream_root.display()
        )));
    }
    let max_segment = *segments.keys().max().unwrap();
    for i in 0..=max_segment {
        if !segments.contains_key(&i) {
            return Err(invalid(format!("segment gap: missing segment {i}")));
        }
    }
    let mut out = Vec::new();
    for (segment, path) in segments {
        let lines = read_segment_lines(&path)?;
        let is_tail = segment == max_segment;
        if is_tail {
            if lines.len() as u64 > SEGMENT_SIZE {
                return Err(invalid(format!(
                    "active segment {segment} exceeds {SEGMENT_SIZE} events"
                )));
            }
        } else if lines.len() as u64 != SEGMENT_SIZE {
            return Err(invalid(format!(
                "closed segment {segment} has {} events, expected {SEGMENT_SIZE}",
                lines.len()
            )));
        }
        out.push(StreamSegmentFile { segment, lines });
    }
    Ok(out)
}

/// Parse every envelope in one agent's stream, checking each line's derived
/// position (segment/offset) agrees with its `seq`/`id`, and that the first
/// event is `agent.registered` at sequence zero.
pub fn read_stream_log(stream_root: &Path, agent: &Agent) -> AbResult<Vec<Envelope>> {
    let files = read_stream_segments(stream_root)?;
    let mut out = Vec::new();
    let mut expected_seq: u64 = 0;
    for file in files {
        for (offset, line) in file.lines.iter().enumerate() {
            let derived_seq = file.segment * SEGMENT_SIZE + offset as u64;
            if derived_seq != expected_seq {
                return Err(invalid(format!(
                    "sequence gap for {agent}: expected {expected_seq}, position implies {derived_seq}"
                )));
            }
            let env = Envelope::parse_line(line)?;
            if env.agent != *agent {
                return Err(invalid(format!(
                    "event in {agent}'s stream has agent field {}",
                    env.agent
                )));
            }
            if env.seq != derived_seq {
                return Err(invalid(format!(
                    "event {} has seq {} but occupies position {derived_seq}",
                    env.id, env.seq
                )));
            }
            out.push(env);
            expected_seq += 1;
        }
    }
    if out.is_empty() {
        return Err(invalid(format!("stream for {agent} has no events")));
    }
    if out[0].seq != 0 || out[0].kind != "agent.registered" {
        return Err(invalid(format!(
            "first event for {agent} must be agent.registered at sequence zero"
        )));
    }
    Ok(out)
}

/// Append one event to a stream's active segment, atomically. Creates a
/// fresh segment file on rollover as needed. The caller is responsible for
/// having derived `env` with the correct next sequence number and for
/// serializing concurrent appends to the same stream (the coordinator's
/// single-actor property, not a file lock here -- ordinary local outbox
/// submission never contends on this).
pub fn append_event(stream_root: &Path, env: &Envelope) -> AbResult<()> {
    fs::create_dir_all(stream_root).map_err(|e| crate::error::AbError::Io {
        path: stream_root.display().to_string(),
        source: e,
    })?;
    let segment = segment_index(env.seq);
    let offset = segment_offset(env.seq);
    let path = segment_path(stream_root, segment);

    let mut existing = String::new();
    if offset != 0 {
        if !path.exists() {
            return Err(invalid(format!(
                "expected existing segment {segment} for {} at offset {offset}",
                env.agent
            )));
        }
        existing = fs::read_to_string(&path).map_err(|e| crate::error::AbError::Io {
            path: path.display().to_string(),
            source: e,
        })?;
    } else if path.exists() {
        return Err(invalid(format!(
            "segment {segment} for {} already exists but a fresh segment was expected",
            env.agent
        )));
    }

    let line = env.to_canonical_line();
    if line.len() > MAX_LINE_BYTES {
        return Err(invalid(format!("event line exceeds {MAX_LINE_BYTES} bytes")));
    }
    existing.push_str(&line);
    existing.push('\n');

    atomic_write(&path, existing.as_bytes())
}

/// Write `contents` to `path` via a same-directory temp file + flush + atomic
/// rename, so a crash cannot publish a partial line (AGENT_BUS.md section 11).
pub fn atomic_write(path: &Path, contents: &[u8]) -> AbResult<()> {
    let dir = path.parent().unwrap_or_else(|| Path::new("."));
    let mut tmp = tempfile::NamedTempFile::new_in(dir).map_err(|e| crate::error::AbError::Io {
        path: dir.display().to_string(),
        source: e,
    })?;
    tmp.write_all(contents)
        .map_err(|e| crate::error::AbError::Io {
            path: path.display().to_string(),
            source: e,
        })?;
    tmp.as_file()
        .sync_all()
        .map_err(|e| crate::error::AbError::Io {
            path: path.display().to_string(),
            source: e,
        })?;
    tmp.persist(path).map_err(|e| crate::error::AbError::Io {
        path: path.display().to_string(),
        source: e.error,
    })?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::AbError;
    use crate::events::{AgentRegistered, AgentStatusEvent, EventData, LifecycleStatus, Role};
    use crate::frontier::ObservedFrontier;
    use crate::scalars::{ObjectId, Short, StringSet, Text};

    fn agent(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn no_frontier() -> ObservedFrontier {
        ObservedFrontier::sparse(ObjectId::parse(format!("{:040x}", 1)).unwrap(), [])
    }

    fn registered_envelope(name: &str, seq: u64) -> Envelope {
        let ag = agent(name);
        let data = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse(name.to_string()).unwrap(),
            primary_role: Role::Implementor,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        Envelope::new(&ag, seq, no_frontier(), &data, [])
    }

    fn status_envelope(name: &str, seq: u64) -> Envelope {
        let ag = agent(name);
        let data = EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: Text::parse("still going".into()).unwrap(),
            product_branch: None,
            product_commit: None,
        });
        Envelope::new(&ag, seq, no_frontier(), &data, [])
    }

    fn write_segment(stream_root: &Path, segment: u64, body: &str) {
        fs::create_dir_all(stream_root).unwrap();
        fs::write(segment_path(stream_root, segment), body).unwrap();
    }

    #[test]
    fn segment_math_rolls_over_at_1000() {
        assert_eq!(segment_index(999), 0);
        assert_eq!(segment_offset(999), 999);
        assert_eq!(segment_index(1000), 1);
        assert_eq!(segment_offset(1000), 0);
        assert_eq!(segment_filename(1), "000001.jsonl");
    }

    #[test]
    fn accepts_well_formed_segment() {
        let lines = read_segment_lines_from_bytes("t", b"{\"a\":1}\n{\"a\":2}\n").unwrap();
        assert_eq!(
            lines,
            vec!["{\"a\":1}".to_string(), "{\"a\":2}".to_string()]
        );
    }

    #[test]
    fn rejects_empty_content() {
        let err = read_segment_lines_from_bytes("t", b"").unwrap_err();
        assert!(err.to_string().contains("empty segment content"));
    }

    #[test]
    fn rejects_byte_order_mark() {
        let mut bytes = vec![0xEF, 0xBB, 0xBF];
        bytes.extend_from_slice(b"{}\n");
        let err = read_segment_lines_from_bytes("t", &bytes).unwrap_err();
        assert!(err.to_string().contains("byte-order mark"));
    }

    #[test]
    fn rejects_body_that_is_only_a_newline() {
        let err = read_segment_lines_from_bytes("t", b"\n").unwrap_err();
        assert!(err.to_string().contains("empty segment content"));
    }

    #[test]
    fn rejects_non_utf8() {
        let err = read_segment_lines_from_bytes("t", &[0xFF, 0xFE, b'\n']).unwrap_err();
        assert!(err.to_string().contains("not UTF-8"));
    }

    #[test]
    fn rejects_line_exceeding_max_bytes() {
        let mut bytes = vec![b'"'];
        bytes.extend(std::iter::repeat_n(b'x', MAX_LINE_BYTES + 10));
        bytes.push(b'"');
        bytes.push(b'\n');
        let err = read_segment_lines_from_bytes("t", &bytes).unwrap_err();
        assert!(err.to_string().contains("line exceeds"));
    }

    #[test]
    fn read_segment_lines_reads_a_real_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("seg.jsonl");
        fs::write(&path, "{\"a\":1}\n").unwrap();
        let lines = read_segment_lines(&path).unwrap();
        assert_eq!(lines, vec!["{\"a\":1}".to_string()]);
    }

    #[test]
    fn read_segment_lines_reports_io_error_for_missing_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("missing.jsonl");
        let err = read_segment_lines(&path).unwrap_err();
        assert!(matches!(err, AbError::Io { .. }));
    }

    #[test]
    fn read_stream_segments_rejects_unexpected_file() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("notes.txt"), "hi").unwrap();
        let err = read_stream_segments(dir.path()).unwrap_err();
        assert!(err.to_string().contains("unexpected file in stream tree"));
    }

    #[test]
    fn read_stream_segments_ignores_the_stream_header() {
        let dir = tempfile::tempdir().unwrap();
        write_segment(dir.path(), 0, "{}\n");
        fs::write(dir.path().join("header.json"), "{}").unwrap();
        assert!(read_stream_segments(dir.path()).is_ok());
    }

    /// `stream_root` is a real checked-out worktree in production (see
    /// `stream.rs::read_stream`), so `.git` sits alongside the segments and
    /// must be ignored, not rejected as an unexpected file.
    #[test]
    fn read_stream_segments_ignores_a_dot_git_entry() {
        let dir = tempfile::tempdir().unwrap();
        write_segment(dir.path(), 0, "{}\n");
        fs::write(dir.path().join(".git"), "gitdir: /elsewhere\n").unwrap();
        assert!(read_stream_segments(dir.path()).is_ok());
    }

    #[test]
    fn read_stream_segments_ignores_the_gitattributes_pin() {
        let dir = tempfile::tempdir().unwrap();
        write_segment(dir.path(), 0, "{}\n");
        fs::write(dir.path().join(".gitattributes"), "*.jsonl -text\n").unwrap();
        assert!(read_stream_segments(dir.path()).is_ok());
    }

    #[test]
    fn read_stream_segments_rejects_malformed_filename() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("12345.jsonl"), "{}\n").unwrap();
        let err = read_stream_segments(dir.path()).unwrap_err();
        assert!(err.to_string().contains("malformed segment filename"));
    }

    #[test]
    fn read_stream_segments_rejects_empty_directory() {
        let dir = tempfile::tempdir().unwrap();
        let err = read_stream_segments(dir.path()).unwrap_err();
        assert!(err.to_string().contains("has no segments"));
    }

    #[test]
    fn read_stream_segments_rejects_a_gap() {
        let dir = tempfile::tempdir().unwrap();
        write_segment(dir.path(), 0, "{}\n");
        write_segment(dir.path(), 2, "{}\n");
        let err = read_stream_segments(dir.path()).unwrap_err();
        assert!(err.to_string().contains("segment gap"));
    }

    #[test]
    fn read_stream_segments_rejects_undersized_closed_segment() {
        let dir = tempfile::tempdir().unwrap();
        write_segment(dir.path(), 0, "{}\n{}\n");
        write_segment(dir.path(), 1, "{}\n");
        let err = read_stream_segments(dir.path()).unwrap_err();
        assert!(err.to_string().contains("has 2 events, expected 1000"));
    }

    #[test]
    fn read_stream_segments_rejects_oversized_tail_segment() {
        let dir = tempfile::tempdir().unwrap();
        let body: String = (0..(SEGMENT_SIZE + 1))
            .map(|i| format!("{{\"n\":{i}}}\n"))
            .collect();
        write_segment(dir.path(), 0, &body);
        let err = read_stream_segments(dir.path()).unwrap_err();
        assert!(err.to_string().contains("exceeds 1000 events"));
    }

    #[test]
    fn read_stream_segments_accepts_closed_plus_tail() {
        let dir = tempfile::tempdir().unwrap();
        let closed: String = (0..SEGMENT_SIZE)
            .map(|i| format!("{{\"n\":{i}}}\n"))
            .collect();
        write_segment(dir.path(), 0, &closed);
        write_segment(dir.path(), 1, "{\"n\":1000}\n{\"n\":1001}\n");
        let segments = read_stream_segments(dir.path()).unwrap();
        assert_eq!(segments.len(), 2);
        assert_eq!(segments[0].lines.len(), 1000);
        assert_eq!(segments[1].lines.len(), 2);
    }

    #[test]
    fn read_stream_segments_reports_io_error_for_missing_directory() {
        let dir = tempfile::tempdir().unwrap();
        let missing = dir.path().join("nope");
        let err = read_stream_segments(&missing).unwrap_err();
        assert!(matches!(err, AbError::Io { .. }));
    }

    #[test]
    fn read_stream_log_round_trips_through_append_event() {
        let dir = tempfile::tempdir().unwrap();
        let ag = agent("alice");
        append_event(dir.path(), &registered_envelope("alice", 0)).unwrap();
        append_event(dir.path(), &status_envelope("alice", 1)).unwrap();
        let log = read_stream_log(dir.path(), &ag).unwrap();
        assert_eq!(log.len(), 2);
        assert_eq!(log[0].kind, "agent.registered");
        assert_eq!(log[1].seq, 1);
    }

    #[test]
    fn read_stream_log_rejects_agent_field_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let bob_event = registered_envelope("bob", 0);
        write_segment(dir.path(), 0, &format!("{}\n", bob_event.to_canonical_line()));
        let err = read_stream_log(dir.path(), &agent("alice")).unwrap_err();
        assert!(err.to_string().contains("has agent field bob"));
    }

    #[test]
    fn read_stream_log_rejects_seq_position_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let ev = registered_envelope("alice", 5);
        write_segment(dir.path(), 0, &format!("{}\n", ev.to_canonical_line()));
        let err = read_stream_log(dir.path(), &agent("alice")).unwrap_err();
        assert!(err
            .to_string()
            .contains("has seq 5 but occupies position 0"));
    }

    #[test]
    fn read_stream_log_rejects_non_registered_first_event() {
        let dir = tempfile::tempdir().unwrap();
        let ev = status_envelope("alice", 0);
        write_segment(dir.path(), 0, &format!("{}\n", ev.to_canonical_line()));
        let err = read_stream_log(dir.path(), &agent("alice")).unwrap_err();
        assert!(err
            .to_string()
            .contains("must be agent.registered at sequence zero"));
    }

    #[test]
    fn append_event_creates_a_fresh_segment() {
        let dir = tempfile::tempdir().unwrap();
        let env = registered_envelope("alice", 0);
        append_event(dir.path(), &env).unwrap();
        let content = fs::read_to_string(segment_path(dir.path(), 0)).unwrap();
        assert_eq!(content, format!("{}\n", env.to_canonical_line()));
    }

    #[test]
    fn append_event_appends_to_an_existing_segment() {
        let dir = tempfile::tempdir().unwrap();
        append_event(dir.path(), &registered_envelope("alice", 0)).unwrap();
        let second = registered_envelope("alice", 1);
        append_event(dir.path(), &second).unwrap();
        let content = fs::read_to_string(segment_path(dir.path(), 0)).unwrap();
        assert_eq!(content.lines().count(), 2);
        assert!(content.ends_with(&format!("{}\n", second.to_canonical_line())));
    }

    #[test]
    fn append_event_rejects_offset_without_existing_segment() {
        let dir = tempfile::tempdir().unwrap();
        let env = registered_envelope("alice", 1);
        let err = append_event(dir.path(), &env).unwrap_err();
        assert!(err.to_string().contains("expected existing segment"));
    }

    #[test]
    fn append_event_rejects_fresh_segment_that_already_exists() {
        let dir = tempfile::tempdir().unwrap();
        write_segment(dir.path(), 0, "{}\n");
        let env = registered_envelope("alice", 0);
        let err = append_event(dir.path(), &env).unwrap_err();
        assert!(err
            .to_string()
            .contains("already exists but a fresh segment was expected"));
    }

    #[test]
    fn append_event_rejects_an_oversized_line() {
        let dir = tempfile::tempdir().unwrap();
        let ag = agent("alice");
        let env = Envelope {
            v: crate::envelope::SCHEMA_VERSION,
            id: crate::scalars::EventId::new(&ag, 0),
            agent: ag.clone(),
            seq: 0,
            time: crate::scalars::Timestamp::now_utc(),
            observed: no_frontier(),
            kind: "agent.registered".to_string(),
            refs: StringSet::default(),
            data: serde_json::json!({ "blob": "x".repeat(MAX_LINE_BYTES + 10) }),
        };
        let err = append_event(dir.path(), &env).unwrap_err();
        assert!(err.to_string().contains("event line exceeds"));
    }

    #[test]
    fn append_event_reports_io_error_when_stream_dir_cannot_be_created() {
        let dir = tempfile::tempdir().unwrap();
        let blocked = dir.path().join("blocked");
        fs::write(&blocked, "not a directory").unwrap();
        let env = registered_envelope("alice", 0);
        let err = append_event(&blocked, &env).unwrap_err();
        assert!(matches!(err, AbError::Io { .. }));
    }

    #[test]
    fn append_event_reports_io_error_when_existing_segment_is_unreadable() {
        let dir = tempfile::tempdir().unwrap();
        // Segment 0 "exists" (as far as `Path::exists` is concerned) but is a
        // directory, not a file, so reading it as a string fails.
        fs::create_dir_all(segment_path(dir.path(), 0)).unwrap();
        let env = registered_envelope("alice", 1);
        let err = append_event(dir.path(), &env).unwrap_err();
        assert!(matches!(err, AbError::Io { .. }));
    }

    #[test]
    fn atomic_write_overwrites_existing_content() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("out.txt");
        atomic_write(&path, b"hello").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "hello");
        atomic_write(&path, b"world").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "world");
    }

    #[test]
    fn atomic_write_reports_io_error_for_missing_parent_directory() {
        let base = tempfile::tempdir().unwrap();
        let missing = base.path().join("does-not-exist").join("out.jsonl");
        let err = atomic_write(&missing, b"hello").unwrap_err();
        assert!(matches!(err, AbError::Io { .. }));
    }

    #[test]
    fn atomic_write_reports_io_error_when_target_is_a_directory() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("out");
        fs::create_dir_all(&path).unwrap();
        let err = atomic_write(&path, b"hello").unwrap_err();
        assert!(matches!(err, AbError::Io { .. }));
    }
}
