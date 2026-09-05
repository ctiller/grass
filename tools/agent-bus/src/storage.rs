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
use std::collections::BTreeSet;
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
///
/// See [`read_stream_segments`] on why the on-disk reader is retained now
/// that production reads streams out of git history instead.
#[allow(dead_code)]
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

/// Classify one entry name found at a stream tree's root.
///
/// `Ok(Some(n))` is segment `n`; `Ok(None)` is a name that legitimately
/// belongs in a stream tree without being a segment; `Err` is junk. `label`
/// names the entry in error messages -- a full filesystem path for an
/// on-disk read, a name plus its commit for a read out of git history.
///
/// A stream tree is read both as a checked-out worktree and directly out of
/// the object database (`read_stream_segments` and
/// `read_stream_segments_at` below), and the two must agree exactly on
/// which names are segments, which are ignored, and which are rejected --
/// so the rule lives here once rather than in each reader. `.git` (a
/// worktree's admin link) and `.gitattributes` (the stream root's `-text`
/// pin for its own segment files) only ever appear on the worktree side,
/// but accepting them from either source costs nothing and keeps a single
/// rule honest.
fn classify_stream_entry(name: &str, label: &str) -> AbResult<Option<u64>> {
    if name == "header.json" || name == ".git" || name == ".gitattributes" {
        return Ok(None);
    }
    if !name.ends_with(".jsonl") {
        return Err(invalid(format!("unexpected file in stream tree: {label}")));
    }
    let stem = &name[..name.len() - ".jsonl".len()];
    if stem.len() != 6 || !stem.chars().all(|c| c.is_ascii_digit()) {
        return Err(invalid(format!("malformed segment filename: {label}")));
    }
    let segment: u64 = stem
        .parse()
        .map_err(|_| invalid(format!("malformed segment number: {name}")))?;
    Ok(Some(segment))
}

/// Check that the discovered segment numbers form a non-empty, contiguous,
/// zero-based run, returning the tail (highest) segment number. `source`
/// names the stream in the "no segments at all" message.
fn check_segment_run(present: &BTreeSet<u64>, source: &str) -> AbResult<u64> {
    let Some(&max_segment) = present.iter().next_back() else {
        return Err(invalid(format!("stream tree has no segments: {source}")));
    };
    for i in 0..=max_segment {
        if !present.contains(&i) {
            return Err(invalid(format!("segment gap: missing segment {i}")));
        }
    }
    Ok(max_segment)
}

/// Check one segment's event count against its position in the run: every
/// closed (non-tail) segment holds exactly `SEGMENT_SIZE` events, and the
/// tail holds no more than that.
fn check_segment_size(segment: u64, is_tail: bool, count: usize) -> AbResult<()> {
    if is_tail {
        if count as u64 > SEGMENT_SIZE {
            return Err(invalid(format!(
                "active segment {segment} exceeds {SEGMENT_SIZE} events"
            )));
        }
    } else if count as u64 != SEGMENT_SIZE {
        return Err(invalid(format!(
            "closed segment {segment} has {count} events, expected {SEGMENT_SIZE}"
        )));
    }
    Ok(())
}

/// Discover and structurally read every segment in one stream's working
/// tree, enforcing contiguous zero-based segment numbers, closed non-tail
/// segments with exactly `SEGMENT_SIZE` events, and a non-empty,
/// non-overflowing tail. `stream_root` is a real checked-out worktree (see
/// `stream.rs`), so `.git` (the worktree's admin link) and `.gitattributes`
/// (the stream root's `-text` pin for its own segment files) are present
/// alongside the header and segments and must be ignored rather than
/// rejected.
///
/// Nothing in production calls this any more: every stream read now goes
/// through [`read_stream_segments_at`], straight out of the object
/// database. It is kept, rather than deleted, because it is the
/// *independent* implementation the git-history reader is differentially
/// tested against -- `blob_and_worktree_readers_agree_*` writes one stream,
/// reads it both ways, and asserts the two agree, which only means anything
/// while both readers exist. (The same reasoning, and the same
/// `#[allow(dead_code)]`, as `gitrepo::mock::MockGit`: used only from
/// `#[cfg(test)]` code that a plain non-test build cannot see.) It is also
/// what the deferred Phase 2 write-path work will read back against.
#[allow(dead_code)]
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
        if let Some(segment) = classify_stream_entry(&name, &path.display().to_string())? {
            segments.insert(segment, path);
        }
    }
    let present: BTreeSet<u64> = segments.keys().copied().collect();
    let max_segment = check_segment_run(&present, &stream_root.display().to_string())?;
    let mut out = Vec::new();
    for (segment, path) in segments {
        let lines = read_segment_lines(&path)?;
        check_segment_size(segment, segment == max_segment, lines.len())?;
        out.push(StreamSegmentFile { segment, lines });
    }
    Ok(out)
}

/// The same discovery and structural validation as [`read_stream_segments`],
/// but reading the segment blobs straight out of the commit `stream_tip`
/// instead of a checked-out worktree.
///
/// This is the whole point of `gitobjects.rs`: a stream's content is a few
/// small blobs at known names in a known tree, so materializing a real
/// worktree just to read them (a `git worktree add`, measured at seconds on
/// the fleet repo) buys nothing. Every rule applied here is the shared one
/// above, so a stream read this way is accepted or rejected identically to
/// the same stream read off disk.
///
/// Note that blob bytes arrive exactly as committed, with none of the
/// `core.autocrlf`/`.gitattributes` line-ending translation a checkout
/// applies -- which matters, because `read_segment_lines_from_bytes` rejects
/// CR bytes outright.
pub fn read_stream_segments_at(
    reader: &dyn crate::gitobjects::ObjectReader,
    stream_tip: &crate::scalars::ObjectId,
) -> AbResult<Vec<StreamSegmentFile>> {
    let mut present = BTreeSet::new();
    for name in reader.list_root_entries(stream_tip)? {
        let label = format!("{name} in commit {stream_tip}");
        if let Some(segment) = classify_stream_entry(&name, &label)? {
            present.insert(segment);
        }
    }
    let max_segment = check_segment_run(&present, &format!("commit {stream_tip}"))?;
    let mut out = Vec::new();
    for segment in present {
        let name = segment_filename(segment);
        let label = format!("{name} in commit {stream_tip}");
        // The name came from this same tree listing a moment ago and the
        // odb is immutable, so an absent blob here is not a stale race --
        // it means the entry is a directory or submodule wearing a segment
        // name, which `read_blob_at` reports as an error rather than
        // absence. `None` is therefore unreachable in practice; refuse it
        // explicitly rather than silently treating it as an empty segment.
        let bytes = reader
            .read_blob_at(stream_tip, &name)?
            .ok_or_else(|| invalid(format!("segment listed but unreadable: {label}")))?;
        let lines = read_segment_lines_from_bytes(&label, &bytes)?;
        check_segment_size(segment, segment == max_segment, lines.len())?;
        out.push(StreamSegmentFile { segment, lines });
    }
    Ok(out)
}

/// Parse every envelope in one agent's stream, checking each line's derived
/// position (segment/offset) agrees with its `seq`/`id`, and that the first
/// event is `agent.registered` at sequence zero.
///
/// See [`read_stream_segments`] on why the on-disk reader is retained now
/// that production reads streams out of git history via
/// [`read_stream_log_at`] instead.
#[allow(dead_code)]
pub fn read_stream_log(stream_root: &Path, agent: &Agent) -> AbResult<Vec<Envelope>> {
    assemble_stream_log(read_stream_segments(stream_root)?, agent)
}

/// [`read_stream_log`] over a stream read out of git history rather than a
/// checked-out worktree.
pub fn read_stream_log_at(
    reader: &dyn crate::gitobjects::ObjectReader,
    stream_tip: &crate::scalars::ObjectId,
    agent: &Agent,
) -> AbResult<Vec<Envelope>> {
    assemble_stream_log(read_stream_segments_at(reader, stream_tip)?, agent)
}

/// The parsing and position/identity cross-checks both readers share, over
/// segments already discovered and structurally validated.
fn assemble_stream_log(files: Vec<StreamSegmentFile>, agent: &Agent) -> AbResult<Vec<Envelope>> {
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
        return Err(invalid(format!(
            "event line exceeds {MAX_LINE_BYTES} bytes"
        )));
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

    // ------------------------- the same table, read out of git history
    //
    // Every case above is restated here against `read_stream_segments_at`,
    // fed by a `FixtureObjectReader` instead of a directory. The point is
    // not that blob reading works -- `gitobjects.rs` covers that -- but
    // that the *validation* is genuinely shared: identical content must be
    // accepted or rejected identically, with the same message, no matter
    // which side it arrived from. A rule that drifted into only one reader
    // would show up here as a mismatch.

    fn tip() -> ObjectId {
        ObjectId::parse("ab".repeat(20)).unwrap()
    }

    /// A stream tree in git history: the `.gitattributes` pin every real
    /// stream root carries, plus whatever segments the case needs.
    fn blob_stream(segments: &[(u64, &str)]) -> crate::gitobjects::FixtureObjectReader {
        let mut r = crate::gitobjects::FixtureObjectReader::new().with_blob(
            &tip(),
            ".gitattributes",
            b"*.jsonl -text\n",
        );
        for (n, body) in segments {
            r = r.with_blob(&tip(), &segment_filename(*n), body.as_bytes());
        }
        r
    }

    #[test]
    fn read_stream_segments_at_rejects_unexpected_file() {
        let r = blob_stream(&[(0, "{}\n")]).with_blob(&tip(), "notes.txt", b"hi");
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("unexpected file in stream tree"));
    }

    #[test]
    fn read_stream_segments_at_ignores_the_stream_header_and_gitattributes_pin() {
        let r = blob_stream(&[(0, "{}\n")]).with_blob(&tip(), "header.json", b"{}");
        assert!(read_stream_segments_at(&r, &tip()).is_ok());
    }

    #[test]
    fn read_stream_segments_at_rejects_malformed_filename() {
        let r = blob_stream(&[]).with_blob(&tip(), "12345.jsonl", b"{}\n");
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("malformed segment filename"));
    }

    #[test]
    fn read_stream_segments_at_rejects_a_tree_with_no_segments() {
        let r = blob_stream(&[]);
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("has no segments"));
    }

    #[test]
    fn read_stream_segments_at_rejects_a_gap() {
        let r = blob_stream(&[(0, "{}\n"), (2, "{}\n")]);
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("segment gap"));
    }

    #[test]
    fn read_stream_segments_at_rejects_undersized_closed_segment() {
        let r = blob_stream(&[(0, "{}\n{}\n"), (1, "{}\n")]);
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("has 2 events, expected 1000"));
    }

    #[test]
    fn read_stream_segments_at_rejects_oversized_tail_segment() {
        let body: String = (0..(SEGMENT_SIZE + 1))
            .map(|i| format!("{{\"n\":{i}}}\n"))
            .collect();
        let r = blob_stream(&[(0, &body)]);
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("exceeds 1000 events"));
    }

    #[test]
    fn read_stream_segments_at_accepts_closed_plus_tail() {
        let closed: String = (0..SEGMENT_SIZE)
            .map(|i| format!("{{\"n\":{i}}}\n"))
            .collect();
        let r = blob_stream(&[(0, &closed), (1, "{\"n\":1000}\n{\"n\":1001}\n")]);
        let segments = read_stream_segments_at(&r, &tip()).unwrap();
        assert_eq!(segments.len(), 2);
        assert_eq!(segments[0].lines.len(), 1000);
        assert_eq!(segments[1].lines.len(), 2);
    }

    /// The byte-level structural rules apply to blobs exactly as to files.
    /// A CR is the one that matters most in practice: a checkout on Windows
    /// can introduce them, a blob read never can, and this pins that a CR
    /// committed into history is still rejected.
    #[test]
    fn read_stream_segments_at_rejects_a_cr_byte_in_a_segment_blob() {
        let r = blob_stream(&[(0, "{}\r\n")]);
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("CR byte"), "got {err}");
    }

    #[test]
    fn read_stream_segments_at_rejects_a_partial_final_line_in_a_segment_blob() {
        let r = blob_stream(&[(0, "{}")]);
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("partial final line"));
    }

    /// Error labels must name the commit, not a filesystem path that does
    /// not exist -- otherwise a malformed stream in history reports a
    /// location nobody can go look at.
    #[test]
    fn read_stream_segments_at_labels_errors_with_the_commit() {
        let r = blob_stream(&[(0, "{}\r\n")]);
        let err = read_stream_segments_at(&r, &tip()).unwrap_err().to_string();
        assert!(err.contains("000000.jsonl"), "got {err}");
        assert!(err.contains(tip().as_str()), "got {err}");
    }

    /// A directory wearing a segment's name is corruption, and must be
    /// refused rather than silently read as an absent or empty segment.
    #[test]
    fn read_stream_segments_at_rejects_a_directory_named_like_a_segment() {
        let r = crate::gitobjects::FixtureObjectReader::new()
            .with_directory(&tip(), &segment_filename(0));
        let err = read_stream_segments_at(&r, &tip()).unwrap_err();
        assert!(err.to_string().contains("is not a file"), "got {err}");
    }

    #[test]
    fn read_stream_segments_at_propagates_an_unresolvable_commit() {
        let r = blob_stream(&[(0, "{}\n")]);
        let other = ObjectId::parse("cd".repeat(20)).unwrap();
        let err = read_stream_segments_at(&r, &other).unwrap_err();
        assert!(matches!(err, AbError::Git(_)), "got {err:?}");
    }

    #[test]
    fn read_stream_log_at_round_trips_events() {
        let r = blob_stream(&[(
            0,
            &format!(
                "{}\n{}\n",
                registered_envelope("alice", 0).to_canonical_line(),
                status_envelope("alice", 1).to_canonical_line()
            ),
        )]);
        let log = read_stream_log_at(&r, &tip(), &agent("alice")).unwrap();
        assert_eq!(log.len(), 2);
        assert_eq!(log[0].kind, "agent.registered");
        assert_eq!(log[1].seq, 1);
    }

    #[test]
    fn read_stream_log_at_rejects_agent_field_mismatch() {
        let r = blob_stream(&[(
            0,
            &format!("{}\n", registered_envelope("bob", 0).to_canonical_line()),
        )]);
        let err = read_stream_log_at(&r, &tip(), &agent("alice")).unwrap_err();
        assert!(err.to_string().contains("has agent field bob"));
    }

    #[test]
    fn read_stream_log_at_rejects_non_registered_first_event() {
        let r = blob_stream(&[(
            0,
            &format!("{}\n", status_envelope("alice", 0).to_canonical_line()),
        )]);
        let err = read_stream_log_at(&r, &tip(), &agent("alice")).unwrap_err();
        assert!(err.to_string().contains("must be agent.registered"));
    }

    #[test]
    fn read_stream_log_at_rejects_seq_position_mismatch() {
        let r = blob_stream(&[(
            0,
            &format!(
                "{}\n{}\n",
                registered_envelope("alice", 0).to_canonical_line(),
                status_envelope("alice", 7).to_canonical_line()
            ),
        )]);
        let err = read_stream_log_at(&r, &tip(), &agent("alice")).unwrap_err();
        assert!(err.to_string().contains("occupies position 1"));
    }

    /// The differential check the on-disk reader is retained for: identical
    /// content, read both ways, must produce identical results -- for
    /// content that is accepted *and* for content that is rejected.
    #[test]
    fn blob_and_worktree_readers_agree_on_accepted_content() {
        let closed: String = (0..SEGMENT_SIZE)
            .map(|i| format!("{{\"n\":{i}}}\n"))
            .collect();
        let cases: Vec<Vec<(u64, String)>> = vec![
            vec![(0, "{\"n\":0}\n".to_string())],
            vec![(0, "{\"a\":1}\n{\"b\":2}\n{\"c\":3}\n".to_string())],
            vec![(0, closed.clone()), (1, "{\"n\":1000}\n".to_string())],
        ];
        for case in cases {
            let dir = tempfile::tempdir().unwrap();
            for (n, body) in &case {
                write_segment(dir.path(), *n, body);
            }
            let refs: Vec<(u64, &str)> = case.iter().map(|(n, b)| (*n, b.as_str())).collect();
            let from_disk = read_stream_segments(dir.path()).unwrap();
            let from_blobs = read_stream_segments_at(&blob_stream(&refs), &tip()).unwrap();
            assert_eq!(from_disk.len(), from_blobs.len());
            for (d, b) in from_disk.iter().zip(&from_blobs) {
                assert_eq!(d.segment, b.segment);
                assert_eq!(d.lines, b.lines);
            }
        }
    }

    #[test]
    fn blob_and_worktree_readers_agree_on_rejected_content() {
        // (segments, the substring both readers must report)
        let cases: Vec<(Vec<(u64, String)>, &str)> = vec![
            (vec![(0, "{}\n".into()), (2, "{}\n".into())], "segment gap"),
            (
                vec![(0, "{}\n{}\n".into()), (1, "{}\n".into())],
                "has 2 events, expected 1000",
            ),
            (vec![(0, "{}\r\n".into())], "CR byte"),
            (vec![(0, "{}".into())], "partial final line"),
            (vec![(0, "{}\n\n{}\n".into())], "blank line"),
        ];
        for (case, needle) in cases {
            let dir = tempfile::tempdir().unwrap();
            for (n, body) in &case {
                write_segment(dir.path(), *n, body);
            }
            let refs: Vec<(u64, &str)> = case.iter().map(|(n, b)| (*n, b.as_str())).collect();
            let disk_err = read_stream_segments(dir.path()).unwrap_err().to_string();
            let blob_err = read_stream_segments_at(&blob_stream(&refs), &tip())
                .unwrap_err()
                .to_string();
            assert!(disk_err.contains(needle), "on-disk: {disk_err}");
            assert!(blob_err.contains(needle), "blob: {blob_err}");
        }
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
        write_segment(
            dir.path(),
            0,
            &format!("{}\n", bob_event.to_canonical_line()),
        );
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
