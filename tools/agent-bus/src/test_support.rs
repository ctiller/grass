//! Shared real-repo and scalar-construction helpers for unit tests in
//! `review_cmds.rs` and `validate_cmd.rs`. Test-only: gated out of the
//! release binary entirely.
//!
//! Two complementary testing styles are used across those modules'
//! `#[cfg(test)] mod tests`:
//!
//! - Pure functions (`review_cmds::verify_authorship`/`reconstruct_candidate`,
//!   `validate_cmd`'s private `linked_validate`) take an explicit `repo: &Path`
//!   (or a `BusCtx`/`BusState` built by hand) and every git call they make
//!   funnels through `gitrepo::run`/`run_stdin`, so those tests install a
//!   [`crate::gitrepo::mock::MockGit`] and never touch a real repository.
//! - The higher-level command handlers (`authorize`, `merge_ready`, `merged`,
//!   `reconcile`, `audit_main`, `validate`) call `BusCtx::load_state`, which
//!   walks real git history through a couple of call sites
//!   (`history::blob_bytes`, `BusCtx::bus_json`) that shell out via a plain
//!   `std::process::Command` rather than `gitrepo::run` and so are *not*
//!   mockable. Those tests use the small real-repository fixture below
//!   instead — the same technique `tests/cli_flow.rs` uses, but calling the
//!   crate's Rust functions directly (instead of spawning the `agent-bus`
//!   binary) so individual error branches can be triggered precisely and
//!   cheaply.

#![cfg(test)]

use crate::bus::{self, BusCtx};
use crate::events::{AgentRegistered, EventData, ReviewNominated, ReviewNominationAccepted, Role};
use crate::scalars::{Agent, Branch, EventId, ObjectId, PathClaim, Short, StringSet, Text};
use std::path::Path;
use std::process::Command as StdCommand;

pub fn a(name: &str) -> Agent {
    Agent::parse(name.to_string()).unwrap()
}

pub fn hash(n: u64) -> String {
    format!("{n:040x}")
}

pub fn oid(n: u64) -> ObjectId {
    ObjectId::parse(hash(n)).unwrap()
}

pub fn git(dir: &Path, args: &[&str]) -> String {
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

/// A throwaway repo with one commit on `main`, ready for `bootstrap`.
pub fn init_repo() -> tempfile::TempDir {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path();
    StdCommand::new("git")
        .args(["init", "--quiet", "-b", "main"])
        .arg(path)
        .status()
        .unwrap();
    git(path, &["config", "user.email", "test@example.com"]);
    git(path, &["config", "user.name", "Test"]);
    std::fs::write(path.join("README.md"), "hello\n").unwrap();
    git(path, &["add", "README.md"]);
    git(path, &["commit", "-q", "-m", "initial"]);
    dir
}

/// Bootstraps the `agent-bus` branch (real, via `bus::bootstrap_init`) with
/// `coordinators`, `product_review_from` set to the repo's current `main`.
pub fn bootstrap(dir: &Path, coordinators: &[&str]) -> BusCtx {
    let root = git(dir, &["rev-parse", "HEAD"]);
    let ctx = BusCtx {
        repo_root: dir.to_path_buf(),
        has_origin: false,
    };
    let coords: Vec<Agent> = coordinators.iter().map(|s| a(s)).collect();
    bus::bootstrap_init(&ctx, &coords, &ObjectId::parse(root).unwrap()).unwrap();
    ctx
}

/// Registers `name` with `role` (a plain implementor/reviewer registration;
/// coordinators must instead be named at `bootstrap` time). A fresh
/// registration's seq-0 event can't go through `bus::publish_event` (which
/// requires the agent to already be known, exactly like the production
/// `register` CLI command's own doc comment explains), so this calls the
/// same `commands::register_new_agent` the CLI command itself uses.
pub fn register(ctx: &BusCtx, name: &str, role: Role) -> Agent {
    let agent = a(name);
    let data = EventData::AgentRegistered(AgentRegistered {
        display_name: Short::parse(name.to_string()).unwrap(),
        primary_role: role,
        purpose: Text::parse("does stuff".into()).unwrap(),
        product_base: None,
        product_branch: None,
        provider: None,
        model: None,
    });
    crate::commands::register_new_agent(ctx, &agent, data).unwrap();
    agent
}

/// Publishes a `review.nominated` directly (bypassing the JSON-file CLI
/// surface, which isn't the thing under test), returning its event id.
pub fn nominate(
    ctx: &BusCtx,
    author: &Agent,
    reviewer: &Agent,
    product_branch: &str,
    review_scope: &[&str],
    required_checks: &[&str],
) -> EventId {
    let data = EventData::ReviewNominated(ReviewNominated {
        authors: StringSet::from_iter(vec![author.clone()]),
        product_branch: Branch::parse(product_branch.to_string()).unwrap(),
        reviewer: reviewer.clone(),
        required_checks: required_checks
            .iter()
            .map(|c| Text::parse(c.to_string()).unwrap())
            .collect(),
        review_scope: StringSet::from_iter(
            review_scope
                .iter()
                .map(|p| PathClaim::parse(p.to_string()).unwrap()),
        ),
        summary: Text::parse("add feature".into()).unwrap(),
        target_branch: Branch::parse("refs/heads/main".to_string()).unwrap(),
        evidence: StringSet::default(),
    });
    bus::publish_event(ctx, author, data, vec![]).unwrap().id
}

/// Publishes `review.nomination_accepted` for `nomination`.
pub fn take(ctx: &BusCtx, reviewer: &Agent, nomination: &EventId) {
    let data = EventData::ReviewNominationAccepted(ReviewNominationAccepted {
        nomination: nomination.clone(),
        note: Text::parse("ok".into()).unwrap(),
    });
    bus::publish_event(ctx, reviewer, data, vec![nomination.clone()]).unwrap();
}

/// Checks out `base` (detached), writes `content` to `path`, and commits it
/// with an `Agent-Bus-Agent: <author>` trailer. Returns the new commit hash.
/// Leaves the repo detached at that commit.
pub fn author_commit(dir: &Path, base: &str, path: &str, content: &str, author: &str) -> String {
    git(dir, &["checkout", "--quiet", "--detach", base]);
    std::fs::write(dir.join(path), content).unwrap();
    git(dir, &["add", path]);
    git(
        dir,
        &[
            "commit",
            "-q",
            "-m",
            &format!("work\n\nAgent-Bus-Agent: {author}"),
        ],
    );
    git(dir, &["rev-parse", "HEAD"])
}

pub fn write_json(dir: &Path, name: &str, value: &serde_json::Value) -> String {
    let path = dir.join(name);
    std::fs::write(&path, serde_json::to_vec(value).unwrap()).unwrap();
    path.to_string_lossy().to_string()
}
