//! Segmented JSONL storage (AGENT_BUS.md section 4).

use crate::envelope::Envelope;
use crate::error::{invalid, AbResult};
use crate::scalars::Agent;
use std::collections::BTreeMap;
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

pub fn agent_dir(bus_root: &Path, agent: &Agent) -> PathBuf {
    bus_root.join(agent.as_str())
}

pub fn segment_path(bus_root: &Path, agent: &Agent, segment: u64) -> PathBuf {
    agent_dir(bus_root, agent).join(segment_filename(segment))
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
    let text = std::str::from_utf8(bytes).map_err(|e| invalid(format!("{label} not UTF-8: {e}")))?;
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
            return Err(invalid(format!("line exceeds {MAX_LINE_BYTES} bytes in {label}")));
        }
        lines.push(line.to_string());
    }
    Ok(lines)
}

pub struct AgentLogFile {
    pub segment: u64,
    pub lines: Vec<String>,
}

/// Discover and structurally read every segment for one agent directory,
/// enforcing contiguous zero-based segment numbers, closed non-tail segments
/// with exactly `SEGMENT_SIZE` events, and a non-empty, non-overflowing tail.
pub fn read_agent_segments(bus_root: &Path, agent: &Agent) -> AbResult<Vec<AgentLogFile>> {
    let dir = agent_dir(bus_root, agent);
    let mut segments: BTreeMap<u64, PathBuf> = BTreeMap::new();
    for entry in fs::read_dir(&dir).map_err(|e| crate::error::AbError::Io {
        path: dir.display().to_string(),
        source: e,
    })? {
        let entry = entry.map_err(|e| crate::error::AbError::Io {
            path: dir.display().to_string(),
            source: e,
        })?;
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if !name.ends_with(".jsonl") {
            return Err(invalid(format!("unexpected file in agent log dir: {}", path.display())));
        }
        let stem = &name[..name.len() - ".jsonl".len()];
        if stem.len() != 6 || !stem.chars().all(|c| c.is_ascii_digit()) {
            return Err(invalid(format!("malformed segment filename: {}", path.display())));
        }
        let segment: u64 = stem.parse().map_err(|_| invalid(format!("malformed segment number: {name}")))?;
        segments.insert(segment, path);
    }
    if segments.is_empty() {
        return Err(invalid(format!("agent log has no segments: {}", dir.display())));
    }
    let max_segment = *segments.keys().max().unwrap();
    for i in 0..=max_segment {
        if !segments.contains_key(&i) {
            return Err(invalid(format!("segment gap: missing segment {i} for agent {agent}")));
        }
    }
    let mut out = Vec::new();
    for (segment, path) in segments {
        let lines = read_segment_lines(&path)?;
        let is_tail = segment == max_segment;
        if is_tail {
            if lines.len() as u64 > SEGMENT_SIZE {
                return Err(invalid(format!("active segment {segment} exceeds {SEGMENT_SIZE} events")));
            }
        } else if lines.len() as u64 != SEGMENT_SIZE {
            return Err(invalid(format!(
                "closed segment {segment} for agent {agent} has {} events, expected {SEGMENT_SIZE}",
                lines.len()
            )));
        }
        out.push(AgentLogFile { segment, lines });
    }
    Ok(out)
}

/// Parse every envelope in an agent's log, checking each line's derived
/// position (segment/offset) agrees with its `seq`/`id`, and that the first
/// event is `agent.registered` at sequence zero.
pub fn read_agent_log(bus_root: &Path, agent: &Agent) -> AbResult<Vec<Envelope>> {
    let files = read_agent_segments(bus_root, agent)?;
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
                    "event in {agent}'s log has agent field {}",
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
        return Err(invalid(format!("agent log for {agent} has no events")));
    }
    if out[0].seq != 0 || out[0].kind != "agent.registered" {
        return Err(invalid(format!(
            "first event for {agent} must be agent.registered at sequence zero"
        )));
    }
    Ok(out)
}

/// Append one event to an agent's active segment, atomically. Creates the
/// agent directory and/or a fresh segment file on rollover as needed. The
/// caller is responsible for holding the cross-process lock and for having
/// derived `env` with the correct next sequence number.
pub fn append_event(bus_root: &Path, env: &Envelope) -> AbResult<()> {
    let dir = agent_dir(bus_root, &env.agent);
    fs::create_dir_all(&dir).map_err(|e| crate::error::AbError::Io {
        path: dir.display().to_string(),
        source: e,
    })?;
    let segment = segment_index(env.seq);
    let offset = segment_offset(env.seq);
    let path = segment_path(bus_root, &env.agent, segment);

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
    tmp.write_all(contents).map_err(|e| crate::error::AbError::Io {
        path: path.display().to_string(),
        source: e,
    })?;
    tmp.as_file().sync_all().map_err(|e| crate::error::AbError::Io {
        path: path.display().to_string(),
        source: e,
    })?;
    tmp.persist(path).map_err(|e| crate::error::AbError::Io {
        path: path.display().to_string(),
        source: e.error,
    })?;
    Ok(())
}

/// List agent directory names present at the bus root (excludes `_bus`).
pub fn list_agents(bus_root: &Path) -> AbResult<Vec<Agent>> {
    let mut out = Vec::new();
    for entry in fs::read_dir(bus_root).map_err(|e| crate::error::AbError::Io {
        path: bus_root.display().to_string(),
        source: e,
    })? {
        let entry = entry.map_err(|e| crate::error::AbError::Io {
            path: bus_root.display().to_string(),
            source: e,
        })?;
        if !entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
            continue;
        }
        let name = entry.file_name().to_string_lossy().to_string();
        if name == "_bus" || name.starts_with('.') {
            continue;
        }
        out.push(Agent::parse(name)?);
    }
    out.sort();
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn segment_math_rolls_over_at_1000() {
        assert_eq!(segment_index(999), 0);
        assert_eq!(segment_offset(999), 999);
        assert_eq!(segment_index(1000), 1);
        assert_eq!(segment_offset(1000), 0);
        assert_eq!(segment_filename(1), "000001.jsonl");
    }

    #[test]
    fn rejects_blank_lines() {
        let err = read_segment_lines_from_bytes("t", b"{}\n\n{}\n").unwrap_err();
        assert!(err.to_string().contains("blank line"));
    }

    #[test]
    fn rejects_cr() {
        let err = read_segment_lines_from_bytes("t", b"{}\r\n").unwrap_err();
        assert!(err.to_string().contains("CR byte"));
    }

    #[test]
    fn rejects_missing_trailing_lf() {
        let err = read_segment_lines_from_bytes("t", b"{}").unwrap_err();
        assert!(err.to_string().contains("partial final line"));
    }

    #[test]
    fn accepts_well_formed_segment() {
        let lines = read_segment_lines_from_bytes("t", b"{\"a\":1}\n{\"a\":2}\n").unwrap();
        assert_eq!(lines, vec!["{\"a\":1}".to_string(), "{\"a\":2}".to_string()]);
    }
}
