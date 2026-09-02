//! Walks the linear `agent-bus` branch commit history, turning each commit
//! into the set of events it newly appended (AGENT_BUS.md section 9's
//! incremental-validation model). This is the single source of "publication
//! order" used everywhere causality/reachability matters, so that no code
//! path has to invent a cross-agent ordering from timestamps.

use crate::bootstrap::BusJson;
use crate::envelope::Envelope;
use crate::error::{invalid, AbResult};
use crate::gitrepo;
use crate::scalars::Agent;
use std::collections::BTreeMap;
use std::path::Path;

pub struct WalkedCommit {
    pub commit: String,
    pub index: usize,
    pub is_bootstrap_root: bool,
    pub is_repair: bool,
    /// The repairing coordinator, for a repair commit (already fully
    /// authority/content-checked by `is_repair_commit`); kept for callers
    /// that want to display or audit which coordinator performed a repair.
    #[allow(dead_code)]
    pub agent: Option<Agent>,
    pub new_events: Vec<Envelope>,
}

pub struct Walk {
    pub commits: Vec<WalkedCommit>,
    pub bus_json: BusJson,
}

/// Full walk from the orphan root through `tip`.
pub fn walk_full(git_dir: &Path, tip: &str) -> AbResult<Walk> {
    let list = gitrepo::run_ok(git_dir, &["rev-list", "--first-parent", "--reverse", tip])?;
    let commits: Vec<&str> = list.lines().collect();
    if commits.is_empty() {
        return Err(invalid("agent-bus branch has no commits"));
    }
    walk_commits(git_dir, &commits, true)
}

/// Incremental walk over `old..new`, requiring `old` to already be a validated
/// bootstrap-descendant commit (bootstrap parsing is skipped). `starting_next_seq`
/// seeds the per-agent sequence counter used for the path/offset/sequence
/// agreement check below (AGENT_BUS.md section 9's structural-validation
/// list); pass each agent's already-replayed next expected sequence number
/// (e.g. from `BusState::agents[..].next_seq` as of `old`).
pub fn walk_incremental(
    git_dir: &Path,
    old: &str,
    new: &str,
    starting_next_seq: BTreeMap<Agent, u64>,
    coordinators: &crate::scalars::StringSet<Agent>,
) -> AbResult<Vec<WalkedCommit>> {
    let range = format!("{old}..{new}");
    let list = gitrepo::run_ok(git_dir, &["rev-list", "--first-parent", "--reverse", &range])?;
    let commits: Vec<&str> = list.lines().collect();
    let mut out = Vec::new();
    let mut next_seq = starting_next_seq;
    for (i, commit) in commits.iter().enumerate() {
        out.push(walk_one_commit(git_dir, commit, i + 1, &mut next_seq, Some(coordinators))?);
    }
    Ok(out)
}

fn walk_commits(git_dir: &Path, commits: &[&str], expect_bootstrap: bool) -> AbResult<Walk> {
    let mut out = Vec::new();
    let mut bus_json = None;
    let mut next_seq: BTreeMap<Agent, u64> = BTreeMap::new();
    for (i, commit) in commits.iter().enumerate() {
        let is_root = i == 0;
        if is_root && expect_bootstrap {
            let (wc, bj) = walk_bootstrap_commit(git_dir, commit)?;
            for agent in bj.coordinators.iter() {
                next_seq.insert(agent.clone(), 1);
            }
            bus_json = Some(bj);
            out.push(wc);
        } else {
            let coordinators = bus_json.as_ref().map(|bj: &BusJson| &bj.coordinators);
            out.push(walk_one_commit(git_dir, commit, i, &mut next_seq, coordinators)?);
        }
    }
    let bus_json = bus_json.ok_or_else(|| invalid("missing bootstrap commit"))?;
    Ok(Walk { commits: out, bus_json })
}

fn blob_bytes(git_dir: &Path, commit: &str, path: &str) -> AbResult<Option<Vec<u8>>> {
    use std::process::Command;
    let out = Command::new("git")
        .arg("-C")
        .arg(git_dir)
        .args(["cat-file", "-p", &format!("{commit}:{path}")])
        .output()
        .map_err(|e| crate::error::AbError::Git(format!("cat-file failed: {e}")))?;
    if out.status.success() {
        Ok(Some(out.stdout))
    } else {
        Ok(None)
    }
}

fn list_tree_files(git_dir: &Path, commit: &str) -> AbResult<Vec<String>> {
    let out = gitrepo::run_ok(git_dir, &["ls-tree", "-r", "--name-only", commit])?;
    Ok(out.lines().map(|s| s.to_string()).collect())
}

fn walk_bootstrap_commit(git_dir: &Path, commit: &str) -> AbResult<(WalkedCommit, BusJson)> {
    let parents = gitrepo::parents_of(git_dir, commit)?;
    if !parents.is_empty() {
        return Err(invalid("bus root commit must have no parent"));
    }
    let files = list_tree_files(git_dir, commit)?;
    let expected_extra = [".gitattributes", "_bus/BUS.json"];
    let bj_bytes = blob_bytes(git_dir, commit, "_bus/BUS.json")?
        .ok_or_else(|| invalid("bootstrap commit missing _bus/BUS.json"))?;
    let bus_json = BusJson::parse(&bj_bytes)?;

    let ga_bytes = blob_bytes(git_dir, commit, ".gitattributes")?
        .ok_or_else(|| invalid("bootstrap commit missing .gitattributes"))?;
    if ga_bytes != crate::bootstrap::GITATTRIBUTES_CONTENTS.as_bytes() {
        return Err(invalid(".gitattributes is not exactly `*.jsonl -text`"));
    }

    let mut new_events = Vec::new();
    let mut seen_agents = std::collections::BTreeSet::new();
    for f in &files {
        if expected_extra.contains(&f.as_str()) {
            continue;
        }
        if !f.ends_with("/000000.jsonl") {
            return Err(invalid(format!("unexpected bootstrap file: {f}")));
        }
        let agent_name = f.trim_end_matches("/000000.jsonl");
        let agent = Agent::parse(agent_name.to_string())?;
        if !bus_json.coordinators.iter().any(|c| c == &agent) {
            return Err(invalid(format!(
                "bootstrap registers {agent} which is not in BUS.json coordinators"
            )));
        }
        let bytes = blob_bytes(git_dir, commit, f)?.ok_or_else(|| invalid(format!("missing {f}")))?;
        let lines = crate::storage::read_segment_lines_from_bytes(f, &bytes)?;
        if lines.len() != 1 {
            return Err(invalid(format!(
                "bootstrap registration file {f} must contain exactly one event"
            )));
        }
        let env = Envelope::parse_line(&lines[0])?;
        if env.seq != 0 || env.kind != "agent.registered" {
            return Err(invalid(format!("{f} must contain agent.registered at seq 0")));
        }
        if env.observed.is_some() {
            return Err(invalid(format!(
                "bootstrap registration {} must have observed: null",
                env.id
            )));
        }
        if env.agent != agent {
            return Err(invalid(format!("{f} event agent field does not match directory")));
        }
        seen_agents.insert(agent.clone());
        new_events.push(env);
    }
    for c in bus_json.coordinators.iter() {
        if !seen_agents.contains(c) {
            return Err(invalid(format!(
                "coordinator {c} named in BUS.json has no bootstrap registration"
            )));
        }
    }

    Ok((
        WalkedCommit {
            commit: commit.to_string(),
            index: 0,
            is_bootstrap_root: true,
            is_repair: false,
            agent: None,
            new_events,
        },
        bus_json,
    ))
}

/// Section 11's sole append-only exception. This is checked here, as part of
/// the structural walk every consumer (`load_state`, `validate`, `sync`,
/// `dry_run`, ...) goes through — not as a separate opt-in pass — so a
/// forged repair commit cannot slip past anything but `validate`.
fn is_repair_commit(
    git_dir: &Path,
    commit: &str,
    parent: &str,
    coordinators: Option<&crate::scalars::StringSet<Agent>>,
) -> AbResult<Option<String>> {
    let msg = gitrepo::run_ok(git_dir, &["show", "-s", "--format=%B", commit])?;
    if !msg.starts_with("bus-admin: repair ") {
        return Ok(None);
    }
    let trailers = gitrepo::commit_message_trailers(git_dir, commit)?;
    let coordinator_trailers: Vec<&(String, String)> =
        trailers.iter().filter(|(k, _)| k == "Agent-Bus-Coordinator").collect();
    if coordinator_trailers.len() != 1 {
        return Err(invalid(format!(
            "repair commit {commit} must have exactly one Agent-Bus-Coordinator trailer, found {}",
            coordinator_trailers.len()
        )));
    }
    let coordinator = coordinator_trailers[0].1.clone();
    let coordinator_agent = Agent::parse(coordinator.clone())?;
    if let Some(coordinators) = coordinators {
        if !coordinators.iter().any(|c| c == &coordinator_agent) {
            return Err(invalid(format!(
                "repair commit {commit} trailer names {coordinator}, which is not a bootstrap coordinator"
            )));
        }
    }

    let first_line = msg.lines().next().unwrap_or("");
    let parts: Vec<&str> = first_line.split_whitespace().collect();
    if parts.len() != 5 || parts[0] != "bus-admin:" || parts[1] != "repair" || parts[3] != "restore" {
        return Err(invalid(format!(
            "repair commit {commit} does not match `bus-admin: repair <invalid-commit> restore <ancestor>`"
        )));
    }
    let invalid_commit = parts[2];
    let ancestor = parts[4];

    // The named ancestor must genuinely be a *strict, proper* ancestor of the
    // commit it claims to restore, not an attacker-chosen throwaway and not
    // the invalid commit itself (which would make the "restoration" vacuous)
    // (AGENT_BUS.md section 11: "restoration of paths ... to their last valid
    // ancestor state").
    if ancestor == invalid_commit {
        return Err(invalid(format!(
            "repair commit {commit}: ancestor {ancestor} must not be the named invalid commit itself"
        )));
    }
    if !gitrepo::is_ancestor(git_dir, ancestor, invalid_commit)? {
        return Err(invalid(format!(
            "repair commit {commit}: {ancestor} is not an ancestor of the named invalid commit {invalid_commit}"
        )));
    }

    // Restore exactly the paths the *invalid* commit changed (relative to
    // its own parent) — not merely whatever paths this repair commit itself
    // happens to touch, which would let a partial restoration pass.
    let invalid_parents = gitrepo::parents_of(git_dir, invalid_commit)?;
    let invalid_parent = invalid_parents
        .first()
        .ok_or_else(|| invalid(format!("repair commit {commit}: named invalid commit {invalid_commit} has no parent")))?;
    let invalid_paths = gitrepo::diff_name_status(git_dir, invalid_parent, invalid_commit)?;
    if invalid_paths.is_empty() {
        return Err(invalid(format!(
            "repair commit {commit}: named invalid commit {invalid_commit} changes nothing"
        )));
    }
    let invalid_path_set: std::collections::BTreeSet<&str> =
        invalid_paths.iter().map(|(_, p)| p.as_str()).collect();
    for (_, path) in &invalid_paths {
        let restored = blob_bytes(git_dir, ancestor, path)?;
        let current = blob_bytes(git_dir, commit, path)?;
        if restored != current {
            return Err(invalid(format!(
                "repair commit {commit} does not byte-for-byte restore {path} from {ancestor}"
            )));
        }
    }

    // The repair commit itself must not touch anything beyond the paths the
    // named invalid commit changed — otherwise it could smuggle in arbitrary,
    // completely unvalidated corruption to unrelated paths (e.g. another
    // agent's log) alongside a legitimate single-path restoration.
    let repair_paths = gitrepo::diff_name_status(git_dir, parent, commit)?;
    for (_, path) in &repair_paths {
        if !invalid_path_set.contains(path.as_str()) {
            return Err(invalid(format!(
                "repair commit {commit} touches {path}, which the named invalid commit {invalid_commit} did not change"
            )));
        }
    }
    Ok(Some(coordinator))
}

fn walk_one_commit(
    git_dir: &Path,
    commit: &str,
    index: usize,
    next_seq: &mut BTreeMap<Agent, u64>,
    coordinators: Option<&crate::scalars::StringSet<Agent>>,
) -> AbResult<WalkedCommit> {
    let parents = gitrepo::parents_of(git_dir, commit)?;
    if parents.len() != 1 {
        return Err(invalid(format!(
            "commit {commit} is not a single-parent commit; agent-bus history must be linear"
        )));
    }
    let parent = &parents[0];

    if let Some(coordinator) = is_repair_commit(git_dir, commit, parent, coordinators)? {
        // Section 11: the sole append-only exception. We do not attempt to
        // replay it as events; validation of its *content* (that it is a
        // byte-for-byte restoration touching only the paths the named
        // invalid commit changed) happens above, inside `is_repair_commit`.
        return Ok(WalkedCommit {
            commit: commit.to_string(),
            index,
            is_bootstrap_root: false,
            is_repair: true,
            agent: Agent::parse(coordinator).ok(),
            new_events: Vec::new(),
        });
    }

    let changes = gitrepo::diff_name_status(git_dir, parent, commit)?;
    if changes.is_empty() {
        return Err(invalid(format!("commit {commit} changes nothing")));
    }
    let mut agent: Option<Agent> = None;
    for (_, path) in &changes {
        let top = path.split('/').next().unwrap_or("");
        let a = Agent::parse(top.to_string())
            .map_err(|_| invalid(format!("commit {commit} touches non-agent path {path}")))?;
        match &agent {
            None => agent = Some(a),
            Some(existing) if *existing == a => {}
            Some(existing) => {
                return Err(invalid(format!(
                    "commit {commit} touches multiple agent directories ({existing}, {a})"
                )))
            }
        }
    }
    let agent = agent.ok_or_else(|| invalid(format!("commit {commit} has no agent directory changes")))?;

    let mut new_events = Vec::new();
    for (status, path) in &changes {
        if status != "A" && status != "M" {
            return Err(invalid(format!(
                "commit {commit} performs disallowed change ({status}) on {path}"
            )));
        }
        // AGENT_BUS.md section 9 (structural): "agreement among path, line
        // offset, agent, sequence, and ID". The segment number is derived
        // from the filename alone here — never trusted from event content —
        // and every appended line's derived position (segment*1000+offset)
        // must equal that event's own `seq`.
        let segment = path
            .strip_prefix(&format!("{agent}/"))
            .and_then(|s| s.strip_suffix(".jsonl"))
            .filter(|s| s.len() == 6 && s.chars().all(|c| c.is_ascii_digit()))
            .and_then(|s| s.parse::<u64>().ok())
            .ok_or_else(|| invalid(format!("commit {commit} touches malformed segment path {path}")))?;

        let old = blob_bytes(git_dir, parent, path)?.unwrap_or_default();
        let new = blob_bytes(git_dir, commit, path)?
            .ok_or_else(|| invalid(format!("commit {commit} missing {path} after change")))?;
        if status == "M" {
            if !new.starts_with(&old) {
                return Err(invalid(format!(
                    "commit {commit} rewrites existing content of {path} instead of appending"
                )));
            }
        } else if !old.is_empty() {
            return Err(invalid(format!("commit {commit} marks existing {path} as added")));
        }
        let old_line_count = if old.is_empty() {
            0
        } else {
            crate::storage::read_segment_lines_from_bytes(path, &old)?.len() as u64
        };
        let appended = &new[old.len()..];
        if appended.is_empty() {
            return Err(invalid(format!("commit {commit} touches {path} without appending")));
        }
        let lines = crate::storage::read_segment_lines_from_bytes(path, appended)?;
        for (i, line) in lines.iter().enumerate() {
            let env = Envelope::parse_line(line)?;
            if env.agent != agent {
                return Err(invalid(format!("event in {path} has agent field {}", env.agent)));
            }
            let derived_seq = segment * crate::storage::SEGMENT_SIZE + old_line_count + i as u64;
            if env.seq != derived_seq {
                return Err(invalid(format!(
                    "event {} occupies position {derived_seq} in {path} (segment {segment}, offset {}) but its seq field says {}",
                    env.id,
                    old_line_count + i as u64,
                    env.seq
                )));
            }
            let expected = next_seq.entry(agent.clone()).or_insert(0);
            if env.seq != *expected {
                return Err(invalid(format!(
                    "event {}: out-of-order or non-contiguous sequence (expected {expected}, got {})",
                    env.id, env.seq
                )));
            }
            *expected += 1;
            new_events.push(env);
        }
    }
    new_events.sort_by_key(|e| e.seq);

    Ok(WalkedCommit {
        commit: commit.to_string(),
        index,
        is_bootstrap_root: false,
        is_repair: false,
        agent: Some(agent),
        new_events,
    })
}
