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

#[derive(Debug)]
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

#[derive(Debug)]
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
    let list = gitrepo::run_ok(
        git_dir,
        &["rev-list", "--first-parent", "--reverse", &range],
    )?;
    let commits: Vec<&str> = list.lines().collect();
    let repair_targets = scan_repair_targets(git_dir, &commits)?;
    let mut out = Vec::new();
    let mut next_seq = starting_next_seq;
    for (i, commit) in commits.iter().enumerate() {
        out.push(walk_one_commit_or_defer(
            git_dir,
            commit,
            i + 1,
            &mut next_seq,
            Some(coordinators),
            &repair_targets,
        )?);
    }
    Ok(out)
}

fn walk_commits(git_dir: &Path, commits: &[&str], expect_bootstrap: bool) -> AbResult<Walk> {
    let repair_targets = scan_repair_targets(git_dir, commits)?;
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
            out.push(walk_one_commit_or_defer(
                git_dir,
                commit,
                i,
                &mut next_seq,
                coordinators,
                &repair_targets,
            )?);
        }
    }
    let bus_json = bus_json.ok_or_else(|| invalid("missing bootstrap commit"))?;
    Ok(Walk {
        commits: out,
        bus_json,
    })
}

/// Cheap, lenient parse of a possible repair-commit message's first line,
/// extracting just the invalid-commit sha it names -- used only to build
/// the deferral map below. A message that merely *looks* malformed here is
/// simply not a repair claim as far as deferral is concerned; `is_repair_
/// commit` still gives it a precise, hard error if the walk ever reaches it
/// as a commit in its own right (this function and that one are
/// deliberately independent, so a bug in this lenient pre-scan can never
/// weaken that function's own strict validation).
fn try_parse_repair_grammar(msg: &str) -> Option<String> {
    let first_line = msg.lines().next()?;
    let parts: Vec<&str> = first_line.split_whitespace().collect();
    if parts.len() == 5 && parts[0] == "bus-admin:" && parts[1] == "repair" && parts[3] == "restore"
    {
        Some(parts[2].to_string())
    } else {
        None
    }
}

/// AGENT_BUS.md section 11: a repair commit may appear *later* in linear
/// history than the invalid commit it fixes, so a single forward walk that
/// aborts the instant it hits a structurally invalid commit would never
/// reach — or even look for — that later repair. This pre-scan (message
/// parsing only, over the same commit range the real walk will process) is
/// what makes that later repair discoverable: it maps each candidate
/// invalid-commit sha to the walk index of the first later commit whose
/// message *claims* to repair it, purely so `walk_one_commit_or_defer` knows
/// which structural failures are even worth deferring judgment on. The
/// claim is never trusted on its own -- see that function's doc comment.
fn scan_repair_targets(git_dir: &Path, commits: &[&str]) -> AbResult<BTreeMap<String, usize>> {
    let mut targets = BTreeMap::new();
    for (i, commit) in commits.iter().enumerate() {
        let msg = gitrepo::run_ok(git_dir, &["show", "-s", "--format=%B", commit])?;
        if let Some(invalid_commit) = try_parse_repair_grammar(&msg) {
            targets.entry(invalid_commit).or_insert(i);
        }
    }
    Ok(targets)
}

/// Wraps `walk_one_commit`: on success, behaves identically. On failure,
/// defers judgment -- treating the commit as contributing no events, rather
/// than aborting the whole walk -- *only if* some later commit in this same
/// range claims (per `scan_repair_targets`) to repair this exact commit.
/// That claim is not taken on faith: when the walk reaches the claimed
/// repair commit's own position (later in this same loop), it goes through
/// the SAME full `is_repair_commit` validation — authority, ancestor,
/// byte-exact restoration, no smuggling — as any other repair commit; if
/// that fails, the walk still aborts there. A bogus "repair" therefore can
/// never excuse a genuinely invalid commit; it only buys the *legitimate*
/// case (a real, later, fully-valid repair) the chance to actually be
/// reached instead of the walk giving up before ever seeing it.
///
/// `next_seq` is only threaded through on success: `walk_one_commit` mutates
/// it incrementally as it accepts each event within a commit, even for a
/// commit that ultimately fails partway through, so deferring a failed
/// commit must not let its partial mutations leak into the real sequence
/// state used to validate every later commit.
fn walk_one_commit_or_defer(
    git_dir: &Path,
    commit: &str,
    index: usize,
    next_seq: &mut BTreeMap<Agent, u64>,
    coordinators: Option<&crate::scalars::StringSet<Agent>>,
    repair_targets: &BTreeMap<String, usize>,
) -> AbResult<WalkedCommit> {
    let mut trial_next_seq = next_seq.clone();
    match walk_one_commit(git_dir, commit, index, &mut trial_next_seq, coordinators) {
        Ok(wc) => {
            *next_seq = trial_next_seq;
            Ok(wc)
        }
        Err(e) => {
            if repair_targets.contains_key(commit) {
                Ok(WalkedCommit {
                    commit: commit.to_string(),
                    index,
                    is_bootstrap_root: false,
                    is_repair: false,
                    agent: None,
                    new_events: Vec::new(),
                })
            } else {
                Err(e)
            }
        }
    }
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
        let bytes =
            blob_bytes(git_dir, commit, f)?.ok_or_else(|| invalid(format!("missing {f}")))?;
        let lines = crate::storage::read_segment_lines_from_bytes(f, &bytes)?;
        if lines.len() != 1 {
            return Err(invalid(format!(
                "bootstrap registration file {f} must contain exactly one event"
            )));
        }
        let env = Envelope::parse_line(&lines[0])?;
        if env.seq != 0 || env.kind != "agent.registered" {
            return Err(invalid(format!(
                "{f} must contain agent.registered at seq 0"
            )));
        }
        if env.observed.is_some() {
            return Err(invalid(format!(
                "bootstrap registration {} must have observed: null",
                env.id
            )));
        }
        if env.agent != agent {
            return Err(invalid(format!(
                "{f} event agent field does not match directory"
            )));
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
    let coordinator_trailers: Vec<&(String, String)> = trailers
        .iter()
        .filter(|(k, _)| k == "Agent-Bus-Coordinator")
        .collect();
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
    if parts.len() != 5 || parts[0] != "bus-admin:" || parts[1] != "repair" || parts[3] != "restore"
    {
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
    let invalid_parent = invalid_parents.first().ok_or_else(|| {
        invalid(format!(
            "repair commit {commit}: named invalid commit {invalid_commit} has no parent"
        ))
    })?;
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
    let agent =
        agent.ok_or_else(|| invalid(format!("commit {commit} has no agent directory changes")))?;

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
            .ok_or_else(|| {
                invalid(format!(
                    "commit {commit} touches malformed segment path {path}"
                ))
            })?;

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
            return Err(invalid(format!(
                "commit {commit} marks existing {path} as added"
            )));
        }
        let old_line_count = if old.is_empty() {
            0
        } else {
            crate::storage::read_segment_lines_from_bytes(path, &old)?.len() as u64
        };
        let appended = &new[old.len()..];
        if appended.is_empty() {
            return Err(invalid(format!(
                "commit {commit} touches {path} without appending"
            )));
        }
        let lines = crate::storage::read_segment_lines_from_bytes(path, appended)?;
        for (i, line) in lines.iter().enumerate() {
            let env = Envelope::parse_line(line)?;
            if env.agent != agent {
                return Err(invalid(format!(
                    "event in {path} has agent field {}",
                    env.agent
                )));
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gitrepo::mock::MockGit;
    use crate::gitrepo::GitOutput;
    use crate::scalars::StringSet;
    use std::path::PathBuf;
    use std::process::Command as StdCommand;

    // -----------------------------------------------------------------
    // is_repair_commit: real, throwaway git repositories in a tempdir.
    //
    // Repair-commit validation is fundamentally about real git object
    // relationships (ancestry, tree diffs, blob content), which
    // `gitrepo::mock::MockGit` cannot fake convincingly here anyway: the
    // content comparisons go through `blob_bytes`, which shells out to
    // `git cat-file` directly rather than through `gitrepo::run`, so it
    // is not interceptable by the mock. Small real commits are simpler
    // and still fast (milliseconds).
    // -----------------------------------------------------------------

    fn git(dir: &Path, args: &[&str]) -> String {
        let out = StdCommand::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .output()
            .expect("git invocation failed");
        assert!(
            out.status.success(),
            "git {args:?} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    }

    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        StdCommand::new("git")
            .args(["init", "--quiet", "-b", "main"])
            .arg(path)
            .status()
            .unwrap();
        git(path, &["config", "user.email", "test@example.com"]);
        git(path, &["config", "user.name", "Test"]);
        dir
    }

    fn write_file(dir: &Path, rel: &str, content: &str) {
        let p = dir.join(rel);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(p, content).unwrap();
    }

    fn commit_all(dir: &Path, msg: &str) -> String {
        git(dir, &["add", "-A"]);
        git(dir, &["commit", "-q", "-m", msg]);
        git(dir, &["rev-parse", "HEAD"])
    }

    fn allow_empty_commit(dir: &Path, msg: &str) -> String {
        git(dir, &["commit", "-q", "--allow-empty", "-m", msg]);
        git(dir, &["rev-parse", "HEAD"])
    }

    fn coordinators(names: &[&str]) -> StringSet<Agent> {
        StringSet::from_iter(names.iter().map(|n| Agent::parse(n.to_string()).unwrap()))
    }

    #[test]
    fn is_repair_commit_returns_none_for_an_ordinary_commit() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let normal = commit_all(dir, "ordinary append, not a repair");
        let result = is_repair_commit(dir, &normal, &base, None).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn is_repair_commit_accepts_a_byte_exact_restoration() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        write_file(dir, "alice/000000.jsonl", "A\n"); // byte-exact restoration
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = commit_all(dir, &msg);
        let coords = coordinators(&["coord1"]);
        let result = is_repair_commit(dir, &repair, &invalid, Some(&coords)).unwrap();
        assert_eq!(result, Some("coord1".to_string()));
    }

    #[test]
    fn is_repair_commit_rejects_self_referential_ancestor() {
        // Regression test: `ancestor == invalid_commit` used to be accepted,
        // making the "restoration" vacuous -- it would "restore" the invalid
        // commit from itself, changing nothing.
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        // No further content change: the self-reference must be rejected
        // before any tree/blob comparison happens.
        let msg = format!(
            "bus-admin: repair {invalid} restore {invalid}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = allow_empty_commit(dir, &msg);
        let err = is_repair_commit(dir, &repair, &invalid, None).unwrap_err();
        assert!(
            err.to_string()
                .contains("must not be the named invalid commit itself"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn is_repair_commit_rejects_smuggled_unrelated_path() {
        // Regression test: a repair commit used to be allowed to touch paths
        // beyond what the named invalid commit changed, because
        // `walk_one_commit` returns early for repair commits and skips every
        // normal structural check -- so a "restoration" of one agent's log
        // could silently also corrupt a completely unrelated agent's log
        // alongside it.
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        // Legitimately restore alice's file...
        write_file(dir, "alice/000000.jsonl", "A\n");
        // ...but also smuggle in an edit to a completely unrelated path that
        // the invalid commit never touched.
        write_file(dir, "bob/000000.jsonl", "sneaky corruption\n");
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = commit_all(dir, &msg);
        let err = is_repair_commit(dir, &repair, &invalid, None).unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains("bob/000000.jsonl") && msg.contains("did not change"),
            "unexpected error: {msg}"
        );
    }

    #[test]
    fn is_repair_commit_rejects_missing_trailer() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        write_file(dir, "alice/000000.jsonl", "A\n");
        let msg = format!("bus-admin: repair {invalid} restore {base}\n");
        let repair = commit_all(dir, &msg);
        let err = is_repair_commit(dir, &repair, &invalid, None).unwrap_err();
        assert!(
            err.to_string()
                .contains("must have exactly one Agent-Bus-Coordinator trailer"),
            "{err}"
        );
    }

    #[test]
    fn is_repair_commit_rejects_multiple_trailers() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        write_file(dir, "alice/000000.jsonl", "A\n");
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\nAgent-Bus-Coordinator: coord2\n"
        );
        let repair = commit_all(dir, &msg);
        let err = is_repair_commit(dir, &repair, &invalid, None).unwrap_err();
        assert!(
            err.to_string()
                .contains("must have exactly one Agent-Bus-Coordinator trailer"),
            "{err}"
        );
    }

    #[test]
    fn is_repair_commit_rejects_coordinator_not_a_bootstrap_coordinator() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        write_file(dir, "alice/000000.jsonl", "A\n");
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = commit_all(dir, &msg);
        let coords = coordinators(&["someone-else"]);
        let err = is_repair_commit(dir, &repair, &invalid, Some(&coords)).unwrap_err();
        assert!(
            err.to_string()
                .contains("which is not a bootstrap coordinator"),
            "{err}"
        );
    }

    #[test]
    fn is_repair_commit_rejects_malformed_grammar() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        // Wrong shape: missing the "restore <ancestor>" tail.
        let msg = "bus-admin: repair not-enough-tokens\n\nAgent-Bus-Coordinator: coord1\n";
        let repair = commit_all(dir, msg);
        // `parent` is only consulted after grammar parsing succeeds, so it
        // doesn't need to resolve to anything for this case.
        let err = is_repair_commit(dir, &repair, "unused", None).unwrap_err();
        assert!(
            err.to_string()
                .contains("does not match `bus-admin: repair"),
            "{err}"
        );
    }

    #[test]
    fn is_repair_commit_rejects_ancestor_that_is_not_actually_an_ancestor() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let _base = commit_all(dir, "base");
        git(dir, &["checkout", "-b", "side"]);
        write_file(dir, "side-only.txt", "side\n");
        let side_tip = commit_all(dir, "side commit");
        git(dir, &["checkout", "main"]);
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        write_file(dir, "alice/000000.jsonl", "A\n");
        let msg = format!(
            "bus-admin: repair {invalid} restore {side_tip}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = commit_all(dir, &msg);
        let err = is_repair_commit(dir, &repair, &invalid, None).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not an ancestor of the named invalid commit"),
            "{err}"
        );
    }

    #[test]
    fn is_repair_commit_rejects_invalid_commit_that_changes_nothing() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        let invalid = allow_empty_commit(dir, "empty, changes nothing");
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = allow_empty_commit(dir, &msg);
        let err = is_repair_commit(dir, &repair, &invalid, None).unwrap_err();
        assert!(err.to_string().contains("changes nothing"), "{err}");
    }

    // -----------------------------------------------------------------
    // walk_one_commit: structural checks on ordinary (non-repair)
    // commits that don't need real blob content -- scripted via
    // `gitrepo::mock::MockGit` instead of a real repository.
    // -----------------------------------------------------------------

    fn any_dir() -> PathBuf {
        PathBuf::from("mock-repo")
    }

    #[test]
    fn walk_one_commit_rejects_non_single_parent_commits() {
        let _guard = MockGit::new()
            .on(&["show", "-s", "--format=%P", "c1"], GitOutput::ok("p1 p2"))
            .install();
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(&any_dir(), "c1", 1, &mut next_seq, None).unwrap_err();
        assert!(
            err.to_string().contains("is not a single-parent commit"),
            "{err}"
        );
    }

    #[test]
    fn walk_one_commit_rejects_a_commit_that_changes_nothing() {
        let _guard = MockGit::new()
            .on(&["show", "-s", "--format=%P", "c1"], GitOutput::ok("p1"))
            .on(
                &["show", "-s", "--format=%B", "c1"],
                GitOutput::ok("an ordinary commit message"),
            )
            .on(&["diff", "--name-status", "p1..c1"], GitOutput::ok(""))
            .install();
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(&any_dir(), "c1", 1, &mut next_seq, None).unwrap_err();
        assert!(err.to_string().contains("changes nothing"), "{err}");
    }

    #[test]
    fn walk_one_commit_rejects_a_non_agent_path() {
        let _guard = MockGit::new()
            .on(&["show", "-s", "--format=%P", "c1"], GitOutput::ok("p1"))
            .on(
                &["show", "-s", "--format=%B", "c1"],
                GitOutput::ok("an ordinary commit message"),
            )
            .on(
                &["diff", "--name-status", "p1..c1"],
                GitOutput::ok("A\tNotAnAgent/000000.jsonl"),
            )
            .install();
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(&any_dir(), "c1", 1, &mut next_seq, None).unwrap_err();
        assert!(err.to_string().contains("touches non-agent path"), "{err}");
    }

    #[test]
    fn walk_one_commit_rejects_multiple_agent_directories() {
        let _guard = MockGit::new()
            .on(&["show", "-s", "--format=%P", "c1"], GitOutput::ok("p1"))
            .on(
                &["show", "-s", "--format=%B", "c1"],
                GitOutput::ok("an ordinary commit message"),
            )
            .on(
                &["diff", "--name-status", "p1..c1"],
                GitOutput::ok("A\talice/000000.jsonl\nM\tbob/000001.jsonl"),
            )
            .install();
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(&any_dir(), "c1", 1, &mut next_seq, None).unwrap_err();
        assert!(
            err.to_string()
                .contains("touches multiple agent directories"),
            "{err}"
        );
    }

    #[test]
    fn walk_one_commit_rejects_a_disallowed_change_type() {
        let _guard = MockGit::new()
            .on(&["show", "-s", "--format=%P", "c1"], GitOutput::ok("p1"))
            .on(
                &["show", "-s", "--format=%B", "c1"],
                GitOutput::ok("an ordinary commit message"),
            )
            .on(
                &["diff", "--name-status", "p1..c1"],
                GitOutput::ok("D\talice/000000.jsonl"),
            )
            .install();
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(&any_dir(), "c1", 1, &mut next_seq, None).unwrap_err();
        assert!(
            err.to_string().contains("performs disallowed change"),
            "{err}"
        );
    }

    #[test]
    fn walk_one_commit_rejects_a_malformed_segment_path() {
        let _guard = MockGit::new()
            .on(&["show", "-s", "--format=%P", "c1"], GitOutput::ok("p1"))
            .on(
                &["show", "-s", "--format=%B", "c1"],
                GitOutput::ok("an ordinary commit message"),
            )
            .on(
                &["diff", "--name-status", "p1..c1"],
                GitOutput::ok("A\talice/not-a-segment.txt"),
            )
            .install();
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(&any_dir(), "c1", 1, &mut next_seq, None).unwrap_err();
        assert!(
            err.to_string().contains("touches malformed segment path"),
            "{err}"
        );
    }

    // -----------------------------------------------------------------
    // is_repair_commit: the byte-for-byte restore-content check, and
    // walk_one_commit's own repair-commit dispatch (real repo -- both
    // depend on `blob_bytes`, so they need real trees/blobs).
    // -----------------------------------------------------------------

    #[test]
    fn is_repair_commit_rejects_a_restoration_that_is_not_byte_exact() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        // Claims to restore alice's file, but doesn't actually reproduce the
        // ancestor's bytes.
        write_file(dir, "alice/000000.jsonl", "A\nX\n");
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = commit_all(dir, &msg);
        let err = is_repair_commit(dir, &repair, &invalid, None).unwrap_err();
        assert!(
            err.to_string().contains("does not byte-for-byte restore"),
            "{err}"
        );
    }

    #[test]
    fn walk_one_commit_recognizes_a_valid_repair_commit() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "A\n");
        let base = commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "A\nB\n");
        let invalid = commit_all(dir, "corrupt append");
        write_file(dir, "alice/000000.jsonl", "A\n");
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = commit_all(dir, &msg);
        let coords = coordinators(&["coord1"]);
        let mut next_seq = BTreeMap::new();
        let wc = walk_one_commit(dir, &repair, 3, &mut next_seq, Some(&coords)).unwrap();
        assert!(wc.is_repair);
        assert!(!wc.is_bootstrap_root);
        assert_eq!(wc.commit, repair);
        assert_eq!(wc.index, 3);
        assert_eq!(wc.agent, Some(Agent::parse("coord1".to_string()).unwrap()));
        assert!(wc.new_events.is_empty());
    }

    // -----------------------------------------------------------------
    // walk_full / walk_incremental: thin `rev-list` + per-commit-walk
    // wrappers, scripted via MockGit.
    // -----------------------------------------------------------------

    #[test]
    fn walk_full_rejects_an_empty_history() {
        let _guard = MockGit::new()
            .on(
                &["rev-list", "--first-parent", "--reverse", "tip"],
                GitOutput::ok(""),
            )
            .install();
        let err = walk_full(&any_dir(), "tip").unwrap_err();
        assert!(err.to_string().contains("has no commits"), "{err}");
    }

    #[test]
    fn walk_incremental_returns_empty_for_an_empty_range() {
        let _guard = MockGit::new()
            .on(
                &["rev-list", "--first-parent", "--reverse", "old..new"],
                GitOutput::ok(""),
            )
            .install();
        let coords = coordinators(&["coord1"]);
        let out = walk_incremental(&any_dir(), "old", "new", BTreeMap::new(), &coords).unwrap();
        assert!(out.is_empty());
    }

    #[test]
    fn walk_incremental_walks_and_propagates_a_per_commit_error() {
        let _guard = MockGit::new()
            .on(
                &["rev-list", "--first-parent", "--reverse", "old..new"],
                GitOutput::ok("c1"),
            )
            .on(&["show", "-s", "--format=%P", "c1"], GitOutput::ok("p1"))
            .on(
                &["show", "-s", "--format=%B", "c1"],
                GitOutput::ok("an ordinary commit message"),
            )
            .on(&["diff", "--name-status", "p1..c1"], GitOutput::ok(""))
            .install();
        let coords = coordinators(&["coord1"]);
        let err = walk_incremental(&any_dir(), "old", "new", BTreeMap::new(), &coords).unwrap_err();
        assert!(err.to_string().contains("changes nothing"), "{err}");
    }

    // -----------------------------------------------------------------
    // walk_bootstrap_commit
    // -----------------------------------------------------------------

    #[test]
    fn walk_bootstrap_commit_rejects_a_root_with_parents() {
        let _guard = MockGit::new()
            .on(&["show", "-s", "--format=%P", "root"], GitOutput::ok("p1"))
            .install();
        let err = walk_bootstrap_commit(&any_dir(), "root").unwrap_err();
        assert!(
            err.to_string()
                .contains("bus root commit must have no parent"),
            "{err}"
        );
    }

    /// A canonically-encoded `agent.registered` line for `ag` at `seq`
    /// (defaulting to `Role::Coordinator`, which is fine for both bootstrap
    /// registrations and the plain append-loop tests below -- the role isn't
    /// consulted by anything in this module).
    fn registered_line(ag: &Agent, seq: u64, observed: Option<crate::scalars::ObjectId>) -> String {
        use crate::events::{AgentRegistered, EventData, Role};
        use crate::scalars::{Short, Text};
        let data = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse(ag.to_string()).unwrap(),
            primary_role: Role::Coordinator,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let env = Envelope::new(ag, seq, observed, &data, []);
        format!("{}\n", env.to_canonical_line())
    }

    fn write_bootstrap_files(dir: &Path, coordinator_names: &[&str]) -> crate::bootstrap::BusJson {
        let coordinators: Vec<Agent> = coordinator_names
            .iter()
            .map(|n| Agent::parse(n.to_string()).unwrap())
            .collect();
        let product_review_from = crate::scalars::ObjectId::parse("0".repeat(40)).unwrap();
        let bus_json = crate::bootstrap::BusJson::new(
            "sha1".to_string(),
            coordinators.clone(),
            product_review_from,
        )
        .expect("git version must match the pinned merge engine version for this test to run");
        write_file(
            dir,
            "_bus/BUS.json",
            &String::from_utf8(bus_json.to_canonical_bytes()).unwrap(),
        );
        write_file(
            dir,
            ".gitattributes",
            crate::bootstrap::GITATTRIBUTES_CONTENTS,
        );
        for c in &coordinators {
            write_file(
                dir,
                &format!("{c}/000000.jsonl"),
                &registered_line(c, 0, None),
            );
        }
        bus_json
    }

    #[test]
    fn walk_bootstrap_commit_accepts_a_well_formed_root() {
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        let root = commit_all(dir, "bootstrap");
        let (wc, bus_json) = walk_bootstrap_commit(dir, &root).unwrap();
        assert!(wc.is_bootstrap_root);
        assert_eq!(wc.new_events.len(), 1);
        assert_eq!(bus_json.coordinators.len(), 1);
    }

    #[test]
    fn walk_bootstrap_commit_rejects_an_unexpected_file() {
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        write_file(dir, "junk.txt", "not part of the bootstrap layout\n");
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string()
                .contains("unexpected bootstrap file: junk.txt"),
            "{err}"
        );
    }

    #[test]
    fn walk_bootstrap_commit_rejects_a_coordinator_missing_its_registration() {
        let repo = init_repo();
        let dir = repo.path();
        // write_bootstrap_files would normally write a registration file per
        // coordinator; build the BUS.json by hand instead so coord2 is named
        // but never gets a `coord2/000000.jsonl`.
        use crate::events::{AgentRegistered, EventData, Role};
        use crate::scalars::{ObjectId, Short, Text};
        let coordinators = vec![
            Agent::parse("coord1".to_string()).unwrap(),
            Agent::parse("coord2".to_string()).unwrap(),
        ];
        let product_review_from = ObjectId::parse("0".repeat(40)).unwrap();
        let bus_json =
            crate::bootstrap::BusJson::new("sha1".to_string(), coordinators, product_review_from)
                .expect(
                    "git version must match the pinned merge engine version for this test to run",
                );
        write_file(
            dir,
            "_bus/BUS.json",
            &String::from_utf8(bus_json.to_canonical_bytes()).unwrap(),
        );
        write_file(
            dir,
            ".gitattributes",
            crate::bootstrap::GITATTRIBUTES_CONTENTS,
        );
        let coord1 = Agent::parse("coord1".to_string()).unwrap();
        let data = EventData::AgentRegistered(AgentRegistered {
            display_name: Short::parse("coord1".into()).unwrap(),
            primary_role: Role::Coordinator,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let env = Envelope::new(&coord1, 0, None, &data, []);
        write_file(
            dir,
            "coord1/000000.jsonl",
            &format!("{}\n", env.to_canonical_line()),
        );
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string().contains("coord2")
                && err.to_string().contains("has no bootstrap registration"),
            "{err}"
        );
    }

    #[test]
    fn walk_bootstrap_commit_rejects_wrong_gitattributes() {
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        write_file(dir, ".gitattributes", "* text=auto\n"); // not the required contents
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string().contains(".gitattributes is not exactly"),
            "{err}"
        );
    }

    #[test]
    fn walk_bootstrap_commit_rejects_registration_for_a_non_coordinator() {
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        // alice is not named in BUS.json's coordinators.
        let alice = Agent::parse("alice".to_string()).unwrap();
        let line = registered_line(&alice, 0, None);
        write_file(dir, "alice/000000.jsonl", &line);
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string().contains("not in BUS.json coordinators"),
            "{err}"
        );
    }

    #[test]
    fn walk_bootstrap_commit_rejects_multiple_events_in_one_registration_file() {
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        let coord1 = Agent::parse("coord1".to_string()).unwrap();
        let mut content = registered_line(&coord1, 0, None);
        content.push_str(&registered_line(&coord1, 0, None));
        write_file(dir, "coord1/000000.jsonl", &content); // two lines, not one
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string().contains("must contain exactly one event"),
            "{err}"
        );
    }

    #[test]
    fn walk_bootstrap_commit_rejects_a_non_registered_first_event() {
        use crate::events::{AgentStatusEvent, EventData, LifecycleStatus};
        use crate::scalars::Text;
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        let coord1 = Agent::parse("coord1".to_string()).unwrap();
        let data = EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: Text::parse("not a registration".into()).unwrap(),
            product_branch: None,
            product_commit: None,
        });
        let env = Envelope::new(&coord1, 0, None, &data, []);
        write_file(
            dir,
            "coord1/000000.jsonl",
            &format!("{}\n", env.to_canonical_line()),
        );
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string()
                .contains("must contain agent.registered at seq 0"),
            "{err}"
        );
    }

    #[test]
    fn walk_bootstrap_commit_rejects_registration_with_an_observed_value() {
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        let coord1 = Agent::parse("coord1".to_string()).unwrap();
        let oid = crate::scalars::ObjectId::parse("1".repeat(40)).unwrap();
        let line = registered_line(&coord1, 0, Some(oid));
        write_file(dir, "coord1/000000.jsonl", &line);
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string().contains("must have observed: null"),
            "{err}"
        );
    }

    #[test]
    fn walk_bootstrap_commit_rejects_registration_agent_field_mismatch() {
        let repo = init_repo();
        let dir = repo.path();
        write_bootstrap_files(dir, &["coord1"]);
        // The file lives under coord1/, but the event inside is bob's --
        // impossible to construct through the normal directory-derived-agent
        // path, but validated defensively here anyway.
        let bob = Agent::parse("bob".to_string()).unwrap();
        let line = registered_line(&bob, 0, None);
        write_file(dir, "coord1/000000.jsonl", &line);
        let root = commit_all(dir, "bootstrap");
        let err = walk_bootstrap_commit(dir, &root).unwrap_err();
        assert!(
            err.to_string()
                .contains("event agent field does not match directory"),
            "{err}"
        );
    }

    // -----------------------------------------------------------------
    // walk_one_commit: the append-content validation loop (needs real
    // blob content, so real repos rather than MockGit).
    // -----------------------------------------------------------------

    #[test]
    fn walk_one_commit_rejects_a_rewrite_disguised_as_an_append() {
        let repo = init_repo();
        let dir = repo.path();
        write_file(dir, "alice/000000.jsonl", "AAAA\n");
        commit_all(dir, "base");
        write_file(dir, "alice/000000.jsonl", "ZZZZ\n"); // not a superset of "AAAA\n"
        let commit = commit_all(dir, "not-a-repair, ordinary looking commit");
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(dir, &commit, 1, &mut next_seq, None).unwrap_err();
        assert!(
            err.to_string().contains("rewrites existing content"),
            "{err}"
        );
    }

    #[test]
    fn walk_one_commit_rejects_an_appended_events_agent_field_mismatch() {
        let repo = init_repo();
        let dir = repo.path();
        let alice = Agent::parse("alice".to_string()).unwrap();
        // Reuse the exact same seq-0 line bytes for the parent and the
        // child's prefix, so the append is byte-for-byte a true append
        // regardless of how long each `registered_line` call takes.
        let seq0 = registered_line(&alice, 0, None);
        write_file(dir, "alice/000000.jsonl", &seq0);
        commit_all(dir, "base");
        let bob = Agent::parse("bob".to_string()).unwrap();
        let content = format!("{seq0}{}", registered_line(&bob, 0, None)); // wrong agent for this path
        write_file(dir, "alice/000000.jsonl", &content);
        let commit = commit_all(dir, "append with wrong agent field");
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(dir, &commit, 1, &mut next_seq, None).unwrap_err();
        assert!(err.to_string().contains("has agent field bob"), "{err}");
    }

    #[test]
    fn walk_one_commit_rejects_an_appended_events_position_mismatch() {
        let repo = init_repo();
        let dir = repo.path();
        let alice = Agent::parse("alice".to_string()).unwrap();
        let seq0 = registered_line(&alice, 0, None);
        write_file(dir, "alice/000000.jsonl", &seq0);
        commit_all(dir, "base");
        // The next line in this file occupies position 1, but claims seq 5.
        let content = format!("{seq0}{}", registered_line(&alice, 5, None));
        write_file(dir, "alice/000000.jsonl", &content);
        let commit = commit_all(dir, "append with wrong seq");
        let mut next_seq = BTreeMap::new();
        let err = walk_one_commit(dir, &commit, 1, &mut next_seq, None).unwrap_err();
        assert!(
            err.to_string().contains("occupies position 1")
                && err.to_string().contains("seq field says 5"),
            "{err}"
        );
    }

    #[test]
    fn walk_one_commit_rejects_an_out_of_order_sequence() {
        let repo = init_repo();
        let dir = repo.path();
        let alice = Agent::parse("alice".to_string()).unwrap();
        let seq0 = registered_line(&alice, 0, None);
        write_file(dir, "alice/000000.jsonl", &seq0);
        commit_all(dir, "base");
        let content = format!("{seq0}{}", registered_line(&alice, 1, None)); // position-correct: occupies seq 1
        write_file(dir, "alice/000000.jsonl", &content);
        let commit = commit_all(dir, "append");
        // Seed the caller's tracked next-expected-sequence as if 5 events had
        // already been replayed for alice, so this position-correct seq-1
        // event is nonetheless out of order relative to the caller's state.
        let mut next_seq = BTreeMap::new();
        next_seq.insert(alice, 5);
        let err = walk_one_commit(dir, &commit, 1, &mut next_seq, None).unwrap_err();
        assert!(
            err.to_string()
                .contains("out-of-order or non-contiguous sequence"),
            "{err}"
        );
    }

    // -----------------------------------------------------------------
    // g-reviewer:6 -- a repair commit *later* in linear history recovering
    // a structurally invalid commit, via `scan_repair_targets`/
    // `walk_one_commit_or_defer`. README.md used to document this as an
    // unrecoverable gap (the forward walk stopped at the invalid commit
    // before ever reaching the repair); these are full `walk_full` runs
    // against a real bootstrapped repo, not just `walk_one_commit` in
    // isolation, so they exercise the actual recovery path a real
    // `agent-bus validate` would take.
    // -----------------------------------------------------------------

    /// Bootstraps, then a real, valid `alice` commit (a well-formed
    /// `agent.registered` envelope line, not arbitrary text -- `walk_full`
    /// actually parses non-repair commits' content as JSON, unlike the
    /// `is_repair_commit`-only tests above which never do). Returns the base
    /// commit sha and the *exact* content string written, so a later
    /// "restoration" can reuse the identical bytes -- `registered_line`
    /// embeds a real wall-clock timestamp, so calling it a second time would
    /// produce different (and thus non-byte-exact) content.
    fn base_bootstrap_and_alice_log(dir: &Path) -> (String, String) {
        write_bootstrap_files(dir, &["coord1"]);
        commit_all(dir, "bootstrap");
        let alice = Agent::parse("alice".to_string()).unwrap();
        let content = registered_line(&alice, 0, None);
        write_file(dir, "alice/000000.jsonl", &content);
        let base = commit_all(dir, "alice base");
        (base, content)
    }

    #[test]
    fn walk_full_recovers_via_a_later_valid_repair_commit() {
        let repo = init_repo();
        let dir = repo.path();
        let (base, content) = base_bootstrap_and_alice_log(dir);

        // A structurally invalid commit: rewrites alice's existing content
        // instead of appending to it.
        write_file(dir, "alice/000000.jsonl", "CORRUPTED\n");
        let invalid = commit_all(dir, "corrupt append");

        // A later, fully valid repair commit restoring it byte-for-byte.
        write_file(dir, "alice/000000.jsonl", &content);
        let msg = format!(
            "bus-admin: repair {invalid} restore {base}\n\nAgent-Bus-Coordinator: coord1\n"
        );
        let repair = commit_all(dir, &msg);

        let walk = walk_full(dir, &repair)
            .expect("a later, fully valid repair commit must let the walk recover");
        assert_eq!(walk.commits.len(), 4, "root, alice-base, invalid, repair");
        let invalid_wc = &walk.commits[2];
        assert_eq!(invalid_wc.commit, invalid);
        assert!(
            !invalid_wc.is_repair,
            "the invalid commit itself is not a repair commit"
        );
        assert!(
            invalid_wc.new_events.is_empty(),
            "a deferred invalid commit must contribute no events"
        );
        let repair_wc = &walk.commits[3];
        assert_eq!(repair_wc.commit, repair);
        assert!(repair_wc.is_repair);
    }

    #[test]
    fn walk_full_still_fails_when_no_repair_claims_the_invalid_commit() {
        let repo = init_repo();
        let dir = repo.path();
        let _ = base_bootstrap_and_alice_log(dir);
        write_file(dir, "alice/000000.jsonl", "CORRUPTED\n");
        let invalid = commit_all(dir, "corrupt append");

        let err = walk_full(dir, &invalid).unwrap_err();
        assert!(
            err.to_string().contains("rewrites existing content"),
            "an invalid commit with no repair claiming it must still fail exactly as before: {err}"
        );
    }

    #[test]
    fn walk_full_still_fails_when_the_claimed_repair_commit_is_itself_invalid() {
        // The deferral claim in `scan_repair_targets` is never trusted on
        // its own: a commit that merely *looks* like a repair (matches the
        // message grammar) but fails `is_repair_commit`'s own validation
        // must not excuse the invalid commit it claims to fix.
        let repo = init_repo();
        let dir = repo.path();
        let (base, content) = base_bootstrap_and_alice_log(dir);
        write_file(dir, "alice/000000.jsonl", "CORRUPTED\n");
        let invalid = commit_all(dir, "corrupt append");

        // Restores the right content, but is missing the required
        // Agent-Bus-Coordinator trailer -- is_repair_commit must reject it.
        write_file(dir, "alice/000000.jsonl", &content);
        let msg = format!("bus-admin: repair {invalid} restore {base}\n");
        let bogus_repair = commit_all(dir, &msg);

        let err = walk_full(dir, &bogus_repair).unwrap_err();
        assert!(
            err.to_string()
                .contains("must have exactly one Agent-Bus-Coordinator trailer"),
            "a bogus claimed repair must fail on its own terms, not be silently accepted: {err}"
        );
    }

    #[test]
    fn scan_repair_targets_ignores_a_message_that_only_resembles_the_grammar() {
        assert_eq!(try_parse_repair_grammar("bus-admin: repair X\n"), None);
        assert_eq!(try_parse_repair_grammar("not a repair message\n"), None);
        assert_eq!(
            try_parse_repair_grammar("bus-admin: repair X restore Y\n"),
            Some("X".to_string())
        );
    }
}
