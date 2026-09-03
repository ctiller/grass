//! End-to-end integration tests for the `agent-bus` CLI (`src/cli.rs`).
//!
//! These drive the actual *compiled binary* (via `assert_cmd`) against
//! disposable git repos built fresh per test (via `tempfile`), mirroring how
//! a real caller would use it: a bare "origin" remote plus one or more
//! ordinary working-repo checkouts. Every test builds its own temp dirs and
//! shells out to the binary as a subprocess, so tests are hermetic and safe
//! to run in parallel (`cargo test`'s default).
//!
//! Two kinds of assertions are used, deliberately:
//!  - Field-level assertions on the parsed JSON, for exact values (an event
//!    id, a rejection reason, a roster's membership).
//!  - `insta` golden snapshots (`INSTA_UPDATE=always cargo test` to accept),
//!    one per distinct CLI output *shape*, with git-object-hash and
//!    timestamp fields redacted via a content-aware dynamic redaction (so a
//!    map's non-hash *keys*, e.g. ref names, are left alone while its hash
//!    *values* are redacted) -- see `redact_noise` below.

use assert_cmd::Command;
use insta::internals::{Content, ContentPath};
use predicates::prelude::*;
use serde_json::Value;
use std::path::Path;
use std::process::Command as StdCommand;
use tempfile::TempDir;

// --------------------------------------------------------------- git/repo setup

fn git(dir: &Path, args: &[&str]) {
    let status = StdCommand::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .status()
        .expect("git must be on PATH");
    assert!(status.success(), "git {args:?} failed in {}", dir.display());
}

/// A forward-slash path string, since a `\`-separated Windows path is not
/// what we want embedded as a git remote path.
fn path_str(p: &Path) -> String {
    p.to_string_lossy().replace('\\', "/")
}

/// A bare "origin" remote, empty until something is genesis'd and pushed to
/// it.
fn init_bare_origin() -> TempDir {
    let dir = tempfile::tempdir().unwrap();
    git(dir.path(), &["init", "--quiet", "--bare", "-b", "main"]);
    dir
}

/// A fresh, ordinary working repo with one commit (so `genesis`'s default
/// `--product-review-from HEAD` resolves to something) and `origin` already
/// pointed at `origin_path` -- exactly the "origin bare repo + working repo
/// with `git remote add origin <bare-path>`" pattern the CLI is designed
/// around.
fn init_repo(origin_path: &Path) -> TempDir {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path();
    git(path, &["init", "--quiet", "-b", "main"]);
    git(path, &["config", "user.email", "test@example.com"]);
    git(path, &["config", "user.name", "Test"]);
    std::fs::write(path.join("README.md"), "hello\n").unwrap();
    git(path, &["add", "README.md"]);
    git(path, &["commit", "-q", "-m", "initial"]);
    git(path, &["remote", "add", "origin", &path_str(origin_path)]);
    dir
}

/// A fresh origin plus one working repo pointed at it -- the common case
/// most tests want and don't need to name separately.
fn fresh_bus() -> (TempDir, TempDir) {
    let origin = init_bare_origin();
    let repo = init_repo(origin.path());
    (origin, repo)
}

// ------------------------------------------------------------------- CLI driving

fn bin() -> Command {
    Command::cargo_bin("agent-bus").expect("agent-bus binary must build")
}

/// Runs `cmd`, asserting a zero exit, and parses stdout as JSON -- every
/// successful `agent-bus` subcommand prints exactly one JSON object.
fn run_json(cmd: &mut Command) -> Value {
    let assert = cmd.assert().success();
    let output = assert.get_output();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "stdout was not valid JSON: {e}\nstdout: {}",
            String::from_utf8_lossy(&output.stdout)
        )
    })
}

fn genesis(repo: &Path, agent: &str, host: &str) -> Value {
    run_json(bin().current_dir(repo).args([
        "genesis",
        "--agent",
        agent,
        "--display-name",
        "Coordinator One",
        "--purpose",
        "bootstraps the bus",
        "--host",
        host,
    ]))
}

#[allow(clippy::too_many_arguments)]
fn register_with(repo: &Path, agent: &str, role: &str, host: &str, standby: Option<&str>) -> Value {
    let mut args = vec![
        "register",
        "--agent",
        agent,
        "--display-name",
        "Some Agent",
        "--role",
        role,
        "--purpose",
        "does agent things",
        "--host",
        host,
    ];
    if let Some(s) = standby {
        args.push("--standby");
        args.push(s);
    }
    run_json(bin().current_dir(repo).args(args))
}

fn register(repo: &Path, agent: &str, role: &str, host: &str) -> Value {
    register_with(repo, agent, role, host, None)
}

fn submit(repo: &Path, agent: &str, kind: &str, data: &str, client_id: &str) -> Value {
    run_json(bin().current_dir(repo).args([
        "submit",
        "--agent",
        agent,
        "--kind",
        kind,
        "--data",
        data,
        "--client-id",
        client_id,
    ]))
}

fn submit_urgent(repo: &Path, agent: &str, kind: &str, data: &str, client_id: &str) -> Value {
    run_json(bin().current_dir(repo).args([
        "submit",
        "--agent",
        agent,
        "--kind",
        kind,
        "--data",
        data,
        "--client-id",
        client_id,
        "--urgent",
    ]))
}

fn outbox(repo: &Path, agent: &str) -> Value {
    run_json(bin().current_dir(repo).args(["outbox", "--agent", agent]))
}

fn coordinate(repo: &Path, agent: &str, host: &str, custody_epoch: u64) -> Value {
    run_json(bin().current_dir(repo).args([
        "coordinate",
        "--agent",
        agent,
        "--host",
        host,
        "--custody-epoch",
        &custody_epoch.to_string(),
    ]))
}

fn tail(repo: &Path, agent: &str) -> Value {
    run_json(bin().current_dir(repo).args(["tail", "--agent", agent]))
}

fn status(repo: &Path, sync: bool) -> Value {
    let mut args = vec!["status"];
    if sync {
        args.push("--sync");
    }
    run_json(bin().current_dir(repo).args(args))
}

fn succeed(repo: &Path, proposer: &str, target: &str, host: &str) -> Value {
    run_json(bin().current_dir(repo).args([
        "succeed",
        "--proposer",
        proposer,
        "--target",
        target,
        "--host",
        host,
    ]))
}

fn prepare_merge(repo: &Path, agent: &str, nomination: &str, reviewed_commit: &str) -> Value {
    run_json(bin().current_dir(repo).args([
        "prepare-merge",
        "--agent",
        agent,
        "--nomination",
        nomination,
        "--reviewed-commit",
        reviewed_commit,
    ]))
}

fn merge_ready(repo: &Path, agent: &str, authorization: &str) -> Value {
    run_json(bin().current_dir(repo).args([
        "merge-ready",
        "--agent",
        agent,
        "--authorization",
        authorization,
    ]))
}

/// Activates the merge engine as `coordinator` (a bootstrap coordinator),
/// naming its own registration event (`<coordinator>:0`) as `previous_epoch`
/// -- the one legitimate "nothing real to reference yet" case
/// `apply_merge_engine_activated` carves out for a fresh bus (see that
/// function's own doc comment). Every active member must already have a
/// published stream before this call (`require_complete_frontier`), so
/// callers run this *after* registering/nominating/accepting, not before.
/// Without a real `merge_engine.activated` event, `review.merge_authorized`
/// can never actually publish (`current_merge_engine_epoch` stays `None`) --
/// see `prepare_merge`'s own tests, which document that gap and stop short
/// of it; `merge-ready`'s tests need a genuinely *published* authorization to
/// exercise, so they close it for real instead.
///
/// Returns the id of the just-published `merge_engine.activated` event
/// itself -- *not* `previous_epoch` -- since that event's own id (not the
/// registration event it names as `previous_epoch`) is what becomes `state.
/// current_merge_engine_epoch`, and therefore what a `review.merge_
/// authorized`'s own `merge_engine_epoch` field must equal
/// (`apply_review_merge_authorized`).
fn activate_merge_engine(repo: &Path, coordinator: &str) -> String {
    let data = serde_json::json!({
        "previous_epoch": format!("{coordinator}:0"),
        "merge_engine": "git-ort",
        "merge_engine_version": "2.53.0",
        "design_commit": "0".repeat(40),
        "helper_commit": "0".repeat(40),
    });
    submit(
        repo,
        coordinator,
        "merge_engine.activated",
        &data.to_string(),
        "activate-merge-engine",
    );
    let coordinated = coordinate(repo, coordinator, "host1", 0);
    assert_eq!(
        coordinated["outbox_rejected"],
        serde_json::json!([]),
        "{coordinated}"
    );
    coordinated["published_events"][0]
        .as_str()
        .unwrap()
        .to_string()
}

/// Submits and coordinates a `review.merge_authorized` event, returning the
/// resulting authorization event id. `merge_engine_epoch` should ordinarily
/// be the id returned by a prior `activate_merge_engine` call.
#[allow(clippy::too_many_arguments)]
fn authorize_merge(
    repo: &Path,
    reviewer: &str,
    nomination: &str,
    previous_main: &str,
    reviewed_commit: &str,
    candidate: &str,
    merge_engine_epoch: &str,
    reviewed_scope: &[&str],
) -> String {
    let data = serde_json::json!({
        "nomination": nomination,
        "product_branch": "refs/heads/agent/zoe/feature",
        "previous_main": previous_main,
        "reviewed_commit": reviewed_commit,
        "candidate": candidate,
        "merge_engine_epoch": merge_engine_epoch,
        "checks": [{"command": "build", "result": "passed"}],
        "finding_dispositions": [],
        "evidence": [],
        "reviewed_scope": reviewed_scope,
        "limitations": [],
        "summary": "looks good",
    });
    submit(
        repo,
        reviewer,
        "review.merge_authorized",
        &data.to_string(),
        "authorize",
    );
    let coordinated = coordinate(repo, reviewer, "host2", 0);
    assert_eq!(
        coordinated["outbox_rejected"],
        serde_json::json!([]),
        "{coordinated}"
    );
    coordinated["published_events"][0]
        .as_str()
        .unwrap()
        .to_string()
}

/// Commits `feature.txt` on top of the repo's current `main`, with an
/// `Agent-Bus-Agent: <trailer_agent>` trailer, and returns `(previous_main,
/// feature_commit)`. Leaves the repo checked out on `main` afterward.
fn commit_feature_with_trailer(repo: &Path, trailer_agent: &str) -> (String, String) {
    let previous_main = crate_rev_parse(repo, "main");
    git(repo, &["checkout", "--quiet", "--detach", &previous_main]);
    std::fs::write(repo.join("feature.txt"), "feature content\n").unwrap();
    git(repo, &["add", "."]);
    git(
        repo,
        &[
            "commit",
            "-q",
            "-m",
            &format!("add feature\n\nAgent-Bus-Agent: {trailer_agent}"),
        ],
    );
    let feature_commit = crate_rev_parse(repo, "HEAD");
    git(repo, &["checkout", "--quiet", "main"]);
    (previous_main, feature_commit)
}

/// Registers `zoe` (implementor) and `aiden` (reviewer), nominates+accepts
/// a review of `feature.txt` naming `aiden` as reviewer, and returns
/// `(nomination_id, previous_main, feature_commit)`. The reviewer's name
/// ("aiden") is deliberately chosen to sort before the author's ("zoe") --
/// see `coordinator.rs`'s own `ReviewFixture` doc comment in the unit test
/// suite for why: `apply.rs`'s cold-reduction ordering does not track a
/// `review.nominated` event's `reviewer` field as a dependency, so a
/// reviewer name that sorts *after* the author's can make a fresh
/// `coordinate` call spuriously fail with "unregistered agent" even though
/// the reviewer really is registered -- a real, separate, pre-existing gap
/// this task does not fix.
fn nominated_and_accepted_review(repo: &Path) -> (String, String, String) {
    register(repo, "aiden", "reviewer", "host2");
    register(repo, "zoe", "implementor", "host2");
    let (previous_main, feature_commit) = commit_feature_with_trailer(repo, "zoe");

    let nominate_data = serde_json::json!({
        "authors": ["zoe"],
        "product_branch": "refs/heads/agent/zoe/feature",
        "reviewer": "aiden",
        "required_checks": ["build"],
        "review_scope": ["feature.txt"],
        "summary": "add feature",
        "target_branch": "refs/heads/main",
        "evidence": [],
    });
    submit(
        repo,
        "zoe",
        "review.nominated",
        &nominate_data.to_string(),
        "nominate",
    );
    let coordinated = coordinate(repo, "zoe", "host2", 0);
    assert_eq!(
        coordinated["outbox_rejected"],
        serde_json::json!([]),
        "{coordinated}"
    );
    let nomination = coordinated["published_events"][0]
        .as_str()
        .unwrap()
        .to_string();

    let accept_data = serde_json::json!({"nomination": nomination, "note": "ok"});
    run_json(bin().current_dir(repo).args([
        "submit",
        "--agent",
        "aiden",
        "--kind",
        "review.nomination_accepted",
        "--data",
        &accept_data.to_string(),
        "--client-id",
        "accept",
        "--observes",
        &nomination,
    ]));
    let accept_coordinated = coordinate(repo, "aiden", "host2", 0);
    assert_eq!(
        accept_coordinated["outbox_rejected"],
        serde_json::json!([]),
        "{accept_coordinated}"
    );

    (nomination, previous_main, feature_commit)
}

fn status_agent<'a>(status_value: &'a Value, agent: &str) -> &'a Value {
    status_value["agents"]
        .as_array()
        .expect("agents is an array")
        .iter()
        .find(|a| a["agent"] == agent)
        .unwrap_or_else(|| panic!("agent {agent} not present in status output: {status_value}"))
}

// -------------------------------------------------------------------- shape checks

fn is_object_hash(s: &str) -> bool {
    (s.len() == 40 || s.len() == 64)
        && s.chars()
            .all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c))
}

fn is_rfc3339_timestamp(s: &str) -> bool {
    let b = s.as_bytes();
    b.len() == 20
        && b[4] == b'-'
        && b[7] == b'-'
        && b[10] == b'T'
        && b[13] == b':'
        && b[16] == b':'
        && b[19] == b'Z'
        && s.chars()
            .enumerate()
            .all(|(i, c)| matches!(i, 4 | 7 | 10 | 13 | 16 | 19) || c.is_ascii_digit())
}

/// A content-aware `insta` dynamic redaction: replaces a value *only* if it
/// looks like a git object hash or an RFC3339 timestamp, and otherwise
/// leaves it untouched. Applying this at a map-entry selector (e.g.
/// `".published.*"`) is safe against `insta`'s own key/value ambiguity there
/// (it visits both a map entry's key and its value at the same selector
/// path) precisely because it is content-, not path-, driven: a ref name
/// key like `refs/heads/agent-registry` never matches either shape and so
/// passes through unredacted, while the hash sitting in the value beside it
/// does get redacted.
fn redact_noise(value: Content, _path: ContentPath<'_>) -> Content {
    if let Some(s) = value.as_str() {
        if is_object_hash(s) {
            return Content::from("[hash]");
        }
        if is_rfc3339_timestamp(s) {
            return Content::from("[time]");
        }
    }
    value
}

// ============================================================ functional tests

/// Requirement 1: `genesis` succeeds and its JSON has the expected
/// registry_epoch/stream_commit/published fields, and those refs actually
/// landed on the remote.
#[test]
fn genesis_reports_expected_fields_and_publishes_both_refs() {
    let (origin, repo) = fresh_bus();
    let out = genesis(repo.path(), "coord1", "host1");

    let registry_epoch = out["registry_epoch"].as_str().unwrap();
    let stream_commit = out["stream_commit"].as_str().unwrap();
    assert!(is_object_hash(registry_epoch), "{registry_epoch}");
    assert!(is_object_hash(stream_commit), "{stream_commit}");
    assert_eq!(out["object_format"], "sha1");
    assert_eq!(out["rejected"], serde_json::json!([]));

    let published = out["published"].as_object().unwrap();
    assert_eq!(
        published
            .get("refs/heads/agent-registry")
            .and_then(|v| v.as_str()),
        Some(registry_epoch)
    );
    assert_eq!(
        published
            .get("refs/heads/agent-events/coord1")
            .and_then(|v| v.as_str()),
        Some(stream_commit)
    );

    // The refs are actually visible on the bare "origin", not merely local.
    let registry_on_origin = crate_rev_parse(origin.path(), "refs/heads/agent-registry");
    assert_eq!(registry_on_origin, registry_epoch);
}

/// `genesis --product-review-from <rev>` is never exercised by any other
/// test -- every other genesis call relies on the default (`HEAD`). Here
/// HEAD and the explicitly named rev deliberately differ, so the recorded
/// `bus_config.json` on the registry root only matches the *named* rev if
/// the flag actually took effect rather than silently defaulting to HEAD.
#[test]
fn genesis_product_review_from_names_an_explicit_rev_not_head() {
    let (_origin, repo) = fresh_bus();
    // `init_repo` already left one commit; add a second so HEAD and the
    // explicitly-named first commit are distinct.
    let first_commit = crate_rev_parse(repo.path(), "HEAD");
    std::fs::write(repo.path().join("second.txt"), "more\n").unwrap();
    git(repo.path(), &["add", "second.txt"]);
    git(repo.path(), &["commit", "-q", "-m", "second"]);
    let head_commit = crate_rev_parse(repo.path(), "HEAD");
    assert_ne!(first_commit, head_commit);

    let out = run_json(bin().current_dir(repo.path()).args([
        "genesis",
        "--agent",
        "coord1",
        "--display-name",
        "Coordinator One",
        "--purpose",
        "bootstraps the bus",
        "--host",
        "host1",
        "--product-review-from",
        &first_commit,
    ]));
    let registry_epoch = out["registry_epoch"].as_str().unwrap();

    let config_json = StdCommand::new("git")
        .arg("-C")
        .arg(repo.path())
        .args(["show", &format!("{registry_epoch}:bus_config.json")])
        .output()
        .unwrap();
    assert!(config_json.status.success());
    let config: Value = serde_json::from_slice(&config_json.stdout).unwrap();
    assert_eq!(config["product_review_from"], first_commit);
    assert_ne!(config["product_review_from"], head_commit);
}

/// Small helper matching the pattern the crate's own tests use for
/// `git rev-parse`, kept local to this test file so this suite never reaches
/// into the crate's internals -- it only ever talks to the compiled binary
/// and to `git` directly.
fn crate_rev_parse(dir: &Path, rev: &str) -> String {
    let out = StdCommand::new("git")
        .arg("-C")
        .arg(dir)
        .args(["rev-parse", rev])
        .output()
        .unwrap();
    assert!(out.status.success(), "git rev-parse {rev} failed");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

/// Requirement 2: `register` adds a second agent, and a completely separate
/// fresh checkout (no prior local state, same origin remote) can
/// `status --sync` and see both agents purely from the remote -- the "no
/// shared mutable state, everything flows through git" property.
#[test]
fn register_then_a_fresh_checkout_sees_both_agents_via_status_sync() {
    let (origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let reg = register(repo.path(), "bob", "reviewer", "host2");

    assert_eq!(reg["published_events"], serde_json::json!(["bob:0"]));
    assert_eq!(reg["outbox_rejected"], serde_json::json!([]));
    assert!(!reg["registry_epoch"].as_str().unwrap().is_empty());

    // A brand-new checkout that has never run any agent-bus command before.
    let fresh = init_repo(origin.path());
    let snap = status(fresh.path(), true);

    assert_eq!(snap["freshness"], "current-as-of-remote-probe");
    let agents = snap["agents"].as_array().unwrap();
    assert_eq!(agents.len(), 2, "{snap}");
    assert_eq!(status_agent(&snap, "coord1")["role"], "coordinator");
    assert_eq!(status_agent(&snap, "bob")["role"], "reviewer");
    assert_eq!(status_agent(&snap, "bob")["host"], "host2");
}

/// Requirement 3: `submit` + `coordinate` publishes an ordinary event, and
/// `tail` shows it.
#[test]
fn submit_and_coordinate_publish_an_event_and_tail_shows_it() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    let submitted = submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "c1",
    );
    assert_eq!(submitted["client_id"], "c1");
    let outbox_path = submitted["outbox_path"].as_str().unwrap();
    assert!(
        Path::new(outbox_path).is_file(),
        "outbox candidate file should exist on disk: {outbox_path}"
    );
    assert!(outbox_path.ends_with("c1.json"), "{outbox_path}");

    let coordinated = coordinate(repo.path(), "coord1", "host1", 0);
    assert_eq!(
        coordinated["published_events"],
        serde_json::json!(["coord1:1"])
    );
    assert_eq!(coordinated["outbox_rejected"], serde_json::json!([]));
    assert_eq!(coordinated["rejected"], serde_json::json!([]));
    assert_eq!(coordinated["not_attempted"], serde_json::json!([]));
    assert!(coordinated["published"]
        .as_object()
        .unwrap()
        .contains_key("refs/heads/agent-events/coord1"));

    let tailed = tail(repo.path(), "coord1");
    assert_eq!(tailed["agent"], "coord1");
    assert_eq!(tailed["activation_event"], Value::Null);
    let events = tailed["events"].as_array().unwrap();
    assert_eq!(events.len(), 2);
    assert_eq!(events[0]["kind"], "agent.registered");
    assert_eq!(events[1]["kind"], "agent.status");
    assert_eq!(events[1]["data"]["status"], "active");
    assert_eq!(events[1]["data"]["note"], "hi");
}

/// `submit --observes <id>` (a cross-agent causal reference) was never
/// exercised by any test. `refs` must exactly equal the ids the event's own
/// data references (`envelope.rs`'s `refs mismatch` check) -- `--observes`
/// is how the CLI caller supplies those, since `submit` has no other way to
/// populate `refs`. Confirms the flag actually reaches the published
/// event's `refs`, not merely accepted and silently dropped.
#[test]
fn submit_observes_records_a_cross_agent_reference() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "bob", "implementor", "host2");

    let issue = submit(
        repo.path(),
        "coord1",
        "issue.opened",
        r#"{"target":"bob","issue_kind":"bug","severity":"normal","summary":"s","locations":[],"reproduction":[],"blocks":[],"evidence":[]}"#,
        "c1",
    );
    coordinate(repo.path(), "coord1", "host1", 0);
    let issue_path = issue["outbox_path"].as_str().unwrap();
    assert!(!issue_path.is_empty());
    let issue_id = "coord1:1";

    run_json(bin().current_dir(repo.path()).args([
        "submit",
        "--agent",
        "bob",
        "--kind",
        "issue.acknowledged",
        "--data",
        &format!(r#"{{"issue":"{issue_id}","assignment":"{issue_id}","note":""}}"#),
        "--client-id",
        "c2",
        "--observes",
        issue_id,
    ]));
    coordinate(repo.path(), "bob", "host2", 0);

    let tailed = tail(repo.path(), "bob");
    let events = tailed["events"].as_array().unwrap();
    assert_eq!(events[1]["kind"], "issue.acknowledged");
    let refs = events[1]["refs"].as_array().unwrap();
    assert_eq!(refs, &vec![serde_json::json!(issue_id)]);
}

/// `tail --sync` fetches `--agent`'s stream from the remote first, rather
/// than reading whatever happens to already be local. A brand-new checkout
/// that has never fetched anything has no local ref for coord1's stream at
/// all, so plain `tail` must fail there, while `tail --sync` must succeed
/// and see everything already published to the origin.
#[test]
fn tail_sync_fetches_the_stream_a_fresh_checkout_has_never_seen() {
    let (origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "c1",
    );
    coordinate(repo.path(), "coord1", "host1", 0);

    let fresh = init_repo(origin.path());
    bin()
        .current_dir(fresh.path())
        .args(["tail", "--agent", "coord1"])
        .assert()
        .failure();

    let synced = run_json(
        bin()
            .current_dir(fresh.path())
            .args(["tail", "--agent", "coord1", "--sync"]),
    );
    assert_eq!(synced["agent"], "coord1");
    let events = synced["events"].as_array().unwrap();
    assert_eq!(events.len(), 2);
    assert_eq!(events[0]["kind"], "agent.registered");
    assert_eq!(events[1]["kind"], "agent.status");
}

/// `outbox` surfaces local outbox state with no network round trip at all
/// (gate 18): before any `coordinate` call, a candidate submitted with
/// `--urgent` is visibly pending and sorted ahead of an ordinary one
/// submitted earlier, exactly the "is my urgent event still waiting"
/// question the command exists to answer.
#[test]
fn outbox_shows_urgent_candidates_pending_and_sorted_first() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"ordinary"}"#,
        "ordinary",
    );
    submit_urgent(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"urgent"}"#,
        "urgent",
    );

    let before = outbox(repo.path(), "coord1");
    let pending = before["pending"].as_array().unwrap();
    assert_eq!(pending.len(), 2);
    assert_eq!(pending[0]["urgent"], true);
    assert!(pending[0]["outbox_path"]
        .as_str()
        .unwrap()
        .ends_with("urgent.json"));
    assert_eq!(pending[1]["urgent"], false);
    assert_eq!(before["rejected"], serde_json::json!([]));

    // coordinate: the urgent candidate must have landed first (coord1:1),
    // the ordinary one second (coord1:2).
    coordinate(repo.path(), "coord1", "host1", 0);
    let tailed = tail(repo.path(), "coord1");
    let events = tailed["events"].as_array().unwrap();
    assert_eq!(events[1]["data"]["note"], "urgent");
    assert_eq!(events[2]["data"]["note"], "ordinary");

    let after = outbox(repo.path(), "coord1");
    assert_eq!(after["pending"], serde_json::json!([]));
}

/// A rejected candidate's durable receipt (kind + reason) shows up under
/// `outbox`'s `rejected` list, not just as a one-time `coordinate` response
/// -- it must stay locally inspectable after the fact.
#[test]
fn outbox_shows_a_rejected_candidates_durable_receipt() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    submit(
        repo.path(),
        "coord1",
        "issue.acknowledged",
        r#"{"issue":"coord1:99","assignment":"coord1:99","note":""}"#,
        "bogus",
    );
    coordinate(repo.path(), "coord1", "host1", 0);

    let after = outbox(repo.path(), "coord1");
    assert_eq!(after["pending"], serde_json::json!([]));
    let rejected = after["rejected"].as_array().unwrap();
    assert_eq!(rejected.len(), 1);
    assert_eq!(rejected[0]["candidate"]["kind"], "issue.acknowledged");
    assert!(rejected[0]["reason"]
        .as_str()
        .unwrap()
        .contains("unknown issue"));
}

/// Requirement 4: a genuinely invalid candidate (referencing a nonexistent
/// issue) is cleanly rejected by `coordinate` -- the specific rejection
/// reason is checked, the rejection receipt actually exists on disk, and a
/// valid candidate submitted alongside it is *not* blocked (still gets a
/// contiguous sequence).
#[test]
fn coordinate_rejects_an_invalid_candidate_without_blocking_valid_ones() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"first"}"#,
        "c1",
    );
    submit(
        repo.path(),
        "coord1",
        "issue.acknowledged",
        r#"{"issue":"coord1:99","assignment":"coord1:99","note":""}"#,
        "c2",
    );
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"third"}"#,
        "c3",
    );

    let out = coordinate(repo.path(), "coord1", "host1", 0);
    assert_eq!(
        out["published_events"],
        serde_json::json!(["coord1:1", "coord1:2"]),
        "the two valid candidates must publish contiguously, skipping the rejected one: {out}"
    );
    let rejected = out["outbox_rejected"].as_array().unwrap();
    assert_eq!(rejected.len(), 1, "{out}");
    assert_eq!(rejected[0]["kind"], "issue.acknowledged");
    assert!(
        rejected[0]["reason"]
            .as_str()
            .unwrap()
            .contains("unknown issue"),
        "{}",
        rejected[0]["reason"]
    );

    // The rejection receipt is durable local evidence on disk, not merely
    // reported in the JSON -- `git_common_dir` for a non-bare, non-worktree
    // repo is simply `<repo>/.git`.
    let rejected_dir = repo
        .path()
        .join(".git")
        .join("agent-bus")
        .join("outbox")
        .join("coord1")
        .join("rejected");
    let entries: Vec<_> = std::fs::read_dir(&rejected_dir)
        .unwrap_or_else(|e| panic!("{}: {e}", rejected_dir.display()))
        .collect();
    assert_eq!(entries.len(), 1, "expected exactly one rejection receipt");
    let receipt: Value =
        serde_json::from_slice(&std::fs::read(entries[0].as_ref().unwrap().path()).unwrap())
            .unwrap();
    assert_eq!(receipt["candidate"]["kind"], "issue.acknowledged");
    assert!(receipt["reason"]
        .as_str()
        .unwrap()
        .contains("unknown issue"));

    // Nothing left pending: the rejected candidate was removed from the
    // active outbox, not left stuck retrying forever.
    let outbox_dir = repo
        .path()
        .join(".git")
        .join("agent-bus")
        .join("outbox")
        .join("coord1");
    let pending: Vec<_> = std::fs::read_dir(&outbox_dir)
        .unwrap()
        .filter(|e| {
            e.as_ref()
                .unwrap()
                .path()
                .extension()
                .and_then(|x| x.to_str())
                == Some("json")
        })
        .collect();
    assert!(pending.is_empty(), "{pending:?}");
}

/// Requirement 5: `register --standby` followed by `succeed` performs
/// coordinator custody succession correctly (gate 19), and the *old*
/// custodian's subsequent `coordinate` attempt is rejected while the *new*
/// custodian succeeds.
#[test]
fn register_standby_then_succeed_moves_custody_and_locks_out_the_old_custodian() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register_with(
        repo.path(),
        "alice",
        "implementor",
        "host-a",
        Some("alice-standby"),
    );

    let succeeded = succeed(repo.path(), "alice-standby", "alice", "host-b");
    assert_eq!(succeeded["new_custody_epoch"], 1);
    assert!(succeeded["registry_published"]
        .as_object()
        .unwrap()
        .contains_key("refs/heads/agent-registry"));
    // Nothing was pending in alice's outbox at succession time.
    assert_eq!(succeeded["resumed_events"], serde_json::json!([]));

    // Something now lands in alice's outbox under the new custody...
    submit(
        repo.path(),
        "alice",
        "agent.status",
        r#"{"status":"active","note":"resumed"}"#,
        "resume-1",
    );

    // ...the *old* custodian (host-a, custody epoch 0) must be refused.
    bin()
        .current_dir(repo.path())
        .args([
            "coordinate",
            "--agent",
            "alice",
            "--host",
            "host-a",
            "--custody-epoch",
            "0",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("belongs to host"));

    // ...while the *new* custodian (host-b, custody epoch 1) succeeds and
    // publishes exactly the preserved outbox entry.
    let out = coordinate(repo.path(), "alice", "host-b", 1);
    assert_eq!(out["published_events"], serde_json::json!(["alice:1"]));
}

/// Round-4 adversarial review, Critical finding: `succeed`'s JSON output
/// used to surface only the `published` half of each of its three
/// publications (registry, resumed outbox, stream), silently dropping any
/// `rejected`/`not_attempted` entries -- unlike `register` and `coordinate`,
/// which surface all of them. An autonomous agent calling `succeed` when
/// something in the resumed outbox is rejected got exit 0 and no
/// explanation. This proves the fields are actually wired, not merely
/// present-and-always-empty: a bogus candidate left in the target's outbox
/// before succession is drained under the new custody and must show up in
/// `resumed_rejected`.
#[test]
fn succeed_surfaces_a_rejected_candidate_from_the_resumed_outbox() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register_with(
        repo.path(),
        "alice",
        "implementor",
        "host-a",
        Some("alice-standby"),
    );

    // A structurally valid but semantically bogus candidate, preserved in
    // alice's local outbox before succession -- the same "unknown issue"
    // recipe `outbox_shows_a_rejected_candidates_durable_receipt` uses.
    submit(
        repo.path(),
        "alice",
        "issue.acknowledged",
        r#"{"issue":"coord1:99","assignment":"coord1:99","note":""}"#,
        "bogus",
    );

    let succeeded = succeed(repo.path(), "alice-standby", "alice", "host-b");
    assert_eq!(succeeded["resumed_events"], serde_json::json!([]));
    let resumed_rejected = succeeded["resumed_rejected"].as_array().unwrap();
    assert_eq!(resumed_rejected.len(), 1);
    assert_eq!(resumed_rejected[0]["kind"], "issue.acknowledged");
    assert!(resumed_rejected[0]["reason"]
        .as_str()
        .unwrap()
        .contains("unknown issue"));

    // The registry and stream publications themselves succeeded cleanly --
    // both `_rejected`/`_not_attempted` fields are present and empty, not
    // merely absent.
    assert_eq!(succeeded["registry_rejected"], serde_json::json!([]));
    assert_eq!(succeeded["registry_not_attempted"], serde_json::json!([]));
    assert_eq!(succeeded["stream_rejected"], serde_json::json!([]));
    assert_eq!(succeeded["stream_not_attempted"], serde_json::json!([]));
}

// ------------------------------------------------- freshness envelope tests
//
// docs/AGENT_COORDINATION_EVOLUTION.md section 2.4: "Every human and
// machine-readable result states its snapshot receipt, roster epoch, causal
// frontier, last successful synchronization time, and freshness class."
// The golden tests above already pin the exact shape for six commands; the
// tests here instead prove the *values* are real and correctly scoped, not
// merely present-and-empty -- an all-null/all-redacted golden snapshot
// would pass even if every field were silently wired to a constant.

/// A fresh checkout's first `status --sync` performs a genuine remote
/// probe: `last_synced` goes from never-recorded to a real timestamp, and a
/// *subsequent* plain (cached) `status` on that same checkout reads back
/// exactly that same recorded value -- proving the record is durable on
/// disk (see `sync::read_last_synced`/`record_last_synced`), not merely
/// returned transiently by the one call that performed the fetch.
#[test]
fn status_sync_records_last_synced_and_a_later_cached_status_reads_it_back() {
    let (origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    let fresh = init_repo(origin.path());
    let synced = status(fresh.path(), true);
    assert_eq!(synced["freshness"], "current-as-of-remote-probe");
    let recorded = synced["last_synced"]
        .as_str()
        .expect("just synced successfully");
    assert!(is_rfc3339_timestamp(recorded), "{recorded}");
    assert!(is_object_hash(synced["roster_epoch"].as_str().unwrap()));
    let receipt = synced["snapshot_receipt"].as_object().unwrap();
    assert!(is_object_hash(receipt["coord1"].as_str().unwrap()));
    assert_eq!(synced["causal_frontier"], synced["snapshot_receipt"]);

    let cached = status(fresh.path(), false);
    assert_eq!(cached["freshness"], "cached");
    assert_eq!(cached["last_synced"].as_str(), Some(recorded));
    assert_eq!(cached["roster_epoch"], synced["roster_epoch"]);
}

/// `tail`'s `snapshot_receipt`/`causal_frontier` are scoped to just the
/// queried agent, not the whole roster -- reporting every other agent's tip
/// on a single-stream read would overstate what `tail` actually looked at.
#[test]
fn tail_scopes_its_freshness_envelope_to_the_queried_agent_only() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "bob", "reviewer", "host2");

    let out = tail(repo.path(), "coord1");
    assert_eq!(out["freshness"], "cached");
    assert!(out["last_synced"].is_null());
    assert!(is_object_hash(out["roster_epoch"].as_str().unwrap()));
    let receipt = out["snapshot_receipt"].as_object().unwrap();
    assert_eq!(receipt.len(), 1, "{out}");
    assert!(is_object_hash(receipt["coord1"].as_str().unwrap()));
    assert_eq!(out["causal_frontier"], out["snapshot_receipt"]);
}

/// `tail --sync` fetches the whole roster cut (see `TailArgs::sync`'s doc
/// comment), so it can honestly report `current-as-of-remote-probe` and a
/// freshly recorded `last_synced`, exactly like `status --sync`.
#[test]
fn tail_sync_reports_current_as_of_remote_probe_and_a_fresh_last_synced() {
    let (origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    let fresh = init_repo(origin.path());
    let out = run_json(
        bin()
            .current_dir(fresh.path())
            .args(["tail", "--agent", "coord1", "--sync"]),
    );
    assert_eq!(out["freshness"], "current-as-of-remote-probe");
    let recorded = out["last_synced"]
        .as_str()
        .expect("just synced successfully");
    assert!(is_rfc3339_timestamp(recorded), "{recorded}");
}

/// `coordinate`'s freshness envelope reflects the just-published local
/// state (`freshness: "cached"`, per its own doc comment in `cli.rs`): a
/// real roster epoch and a real stream tip for the coordinated agent, not
/// null or empty placeholders.
#[test]
fn coordinate_reports_a_populated_freshness_envelope() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "c1",
    );
    let out = coordinate(repo.path(), "coord1", "host1", 0);
    assert_eq!(out["freshness"], "cached");
    assert!(out["last_synced"].is_null());
    assert!(is_object_hash(out["roster_epoch"].as_str().unwrap()));
    let receipt = out["snapshot_receipt"].as_object().unwrap();
    assert!(is_object_hash(receipt["coord1"].as_str().unwrap()));
    assert_eq!(out["causal_frontier"], out["snapshot_receipt"]);
}

/// `register`'s freshness envelope reflects the *post*-registration roster
/// (both the pre-existing coordinator and the just-registered agent), and
/// its `roster_epoch` agrees with the same transition's own `registry_
/// epoch` field -- both describe the one epoch `register` just published.
#[test]
fn register_reports_a_populated_freshness_envelope_reflecting_the_new_roster() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let out = register(repo.path(), "bob", "reviewer", "host2");
    assert_eq!(out["freshness"], "cached");
    assert!(out["last_synced"].is_null());
    assert_eq!(out["roster_epoch"], out["registry_epoch"]);
    let receipt = out["snapshot_receipt"].as_object().unwrap();
    assert_eq!(receipt.len(), 2, "{out}");
    assert!(is_object_hash(receipt["coord1"].as_str().unwrap()));
    assert!(is_object_hash(receipt["bob"].as_str().unwrap()));
}

/// `succeed`'s freshness envelope likewise reflects the post-succession
/// roster (both the coordinator and the agent whose custody just moved).
#[test]
fn succeed_reports_a_populated_freshness_envelope_reflecting_the_post_succession_roster() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register_with(
        repo.path(),
        "alice",
        "implementor",
        "host-a",
        Some("alice-standby"),
    );
    let out = succeed(repo.path(), "alice-standby", "alice", "host-b");
    assert_eq!(out["freshness"], "cached");
    assert!(out["last_synced"].is_null());
    assert_eq!(out["roster_epoch"], out["registry_epoch"]);
    let receipt = out["snapshot_receipt"].as_object().unwrap();
    assert!(is_object_hash(receipt["coord1"].as_str().unwrap()));
    assert!(is_object_hash(receipt["alice"].as_str().unwrap()));
}

/// `outbox` (gate 8/18: a purely local read, no network round trip ever)
/// still reports a populated freshness envelope once a registry exists
/// locally to read it from.
#[test]
fn outbox_reports_a_populated_freshness_envelope_once_a_registry_exists() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "c1",
    );

    let out = outbox(repo.path(), "coord1");
    assert_eq!(out["freshness"], "cached");
    assert!(out["last_synced"].is_null());
    assert!(is_object_hash(out["roster_epoch"].as_str().unwrap()));
    let receipt = out["snapshot_receipt"].as_object().unwrap();
    assert!(is_object_hash(receipt["coord1"].as_str().unwrap()));
    assert_eq!(out["causal_frontier"], out["snapshot_receipt"]);
}

/// `outbox` must keep working exactly as before `genesis` has ever run
/// locally (`submit` itself requires no prior registry at all) -- the
/// roster-wide envelope fields are honestly `null`/empty rather than this
/// command now refusing to show local outbox state it could always show.
#[test]
fn outbox_reports_null_roster_fields_before_genesis_ever_runs() {
    let (_origin, repo) = fresh_bus();
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "c1",
    );

    let out = outbox(repo.path(), "coord1");
    assert_eq!(out["freshness"], "cached");
    assert!(out["last_synced"].is_null());
    assert!(out["roster_epoch"].is_null());
    assert_eq!(out["snapshot_receipt"], serde_json::json!({}));
    assert_eq!(out["causal_frontier"], serde_json::json!({}));
    let pending = out["pending"].as_array().unwrap();
    assert_eq!(pending.len(), 1, "{out}");
}

// ---------------------------------------------------------- error-path tests
//
// Every case here is also reviewed (see the final report) for whether the
// message actually helps a *calling agent* -- not a human -- recover
// autonomously: does it say what to do next, or only what went wrong?

/// Requirement 6: duplicate registration is refused.
#[test]
fn register_rejects_a_duplicate_agent_name() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "bob", "reviewer", "host2");

    bin()
        .current_dir(repo.path())
        .args([
            "register",
            "--agent",
            "bob",
            "--display-name",
            "Bob Again",
            "--role",
            "reviewer",
            "--purpose",
            "duplicate",
            "--host",
            "host3",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("already an active member"));
}

/// Requirement 6: an unknown event kind in `submit` is refused before it
/// ever reaches the outbox.
#[test]
fn submit_rejects_an_unknown_event_kind() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    bin()
        .current_dir(repo.path())
        .args([
            "submit",
            "--agent",
            "coord1",
            "--kind",
            "bogus.kind",
            "--data",
            "{}",
            "--client-id",
            "c1",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("unknown event kind"));
}

/// Requirement 6: an unauthorized agent (neither the target's standby nor
/// an existing coordinator) cannot `succeed` another agent's custody.
#[test]
fn succeed_rejects_an_unauthorized_proposer() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "alice", "implementor", "host-a");
    register(repo.path(), "mallory", "implementor", "host-m");

    bin()
        .current_dir(repo.path())
        .args([
            "succeed",
            "--proposer",
            "mallory",
            "--target",
            "alice",
            "--host",
            "host-m",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("is not authorized"));
}

// ------------------------------------------------------- adversarial tests

/// Adversarial/genesis: a second genesis in the same repo must be refused --
/// there is exactly one registry root, ever.
#[test]
fn genesis_rejects_a_second_root_in_the_same_repo() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    bin()
        .current_dir(repo.path())
        .args([
            "genesis",
            "--agent",
            "coord2",
            "--display-name",
            "Coordinator Two",
            "--purpose",
            "should not be allowed",
            "--host",
            "host2",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("already has a root epoch"));
}

/// Adversarial/register: an agent name that fails the identity grammar
/// (`[a-z][a-z0-9-]{0,47}`) is refused before any registry mutation is even
/// attempted.
#[test]
fn register_rejects_a_syntactically_invalid_agent_name() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    bin()
        .current_dir(repo.path())
        .args([
            "register",
            "--agent",
            "Alice",
            "--display-name",
            "Alice",
            "--role",
            "implementor",
            "--purpose",
            "x",
            "--host",
            "host-a",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("invalid agent name"));
}

/// Adversarial/submit: malformed JSON in `--data` is refused, not
/// interpreted as some empty/default payload.
#[test]
fn submit_rejects_malformed_json_in_data() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    bin()
        .current_dir(repo.path())
        .args([
            "submit",
            "--agent",
            "coord1",
            "--kind",
            "agent.status",
            "--data",
            "{this is not json",
            "--client-id",
            "c1",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("--data is not valid JSON"));
}

/// Adversarial/coordinate: a caller claiming the wrong custody epoch, or the
/// wrong host, for an otherwise-real agent is refused (gate 6/7's
/// precondition) rather than racing onto the stream ref.
#[test]
fn coordinate_rejects_a_stale_or_wrong_custodian() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"x"}"#,
        "c1",
    );

    bin()
        .current_dir(repo.path())
        .args([
            "coordinate",
            "--agent",
            "coord1",
            "--host",
            "host1",
            "--custody-epoch",
            "99",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("belongs to host"));

    bin()
        .current_dir(repo.path())
        .args([
            "coordinate",
            "--agent",
            "coord1",
            "--host",
            "wrong-host",
            "--custody-epoch",
            "0",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("belongs to host"));
}

/// Adversarial/succeed: a target that was never registered (or has since
/// left the current epoch) is refused, not silently treated as a fresh
/// registration.
#[test]
fn succeed_rejects_a_target_outside_the_registry() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    bin()
        .current_dir(repo.path())
        .args([
            "succeed",
            "--proposer",
            "coord1",
            "--target",
            "ghost",
            "--host",
            "host2",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("not an active member"));
}

/// Adversarial/tail: reading a stream for an agent that never registered
/// fails cleanly rather than returning an empty log.
#[test]
fn tail_of_an_unregistered_agent_fails_cleanly() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    bin()
        .current_dir(repo.path())
        .args(["tail", "--agent", "ghost"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("has no stream"));
}

/// AGENT_REVIEW.md section 7 step 4: `prepare-merge` reconstructs the exact
/// no-conflict candidate, tags it `agent-candidate/<reviewer>/<candidate>`,
/// and pushes that tag to `origin` -- confirmed here not just by the CLI's
/// own JSON but by an independent `git ls-remote` against the bare origin
/// repo, so a bug that tagged locally but silently skipped (or malformed)
/// the push would still be caught even if the printed JSON looked right.
#[test]
fn prepare_merge_constructs_and_pushes_the_candidate_tag() {
    let (origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let (nomination, previous_main, feature_commit) = nominated_and_accepted_review(repo.path());

    let out = prepare_merge(repo.path(), "aiden", &nomination, &feature_commit);
    assert_eq!(out["previous_main"], previous_main);
    let candidate = out["candidate"].as_str().expect("candidate is a string");
    assert!(is_object_hash(candidate), "{candidate}");
    // No `merge_engine.activated` event exists in this fixture -- a real,
    // separate, pre-existing gap in this bus with no production path that
    // can ever populate `current_merge_engine_epoch` at all (see this
    // task's final report) -- so this is honestly `null`, not a bug in
    // `prepare-merge` itself.
    assert_eq!(out["merge_engine_epoch"], Value::Null);

    let tag_ref = format!("refs/tags/agent-candidate/aiden/{candidate}");
    let remote_listing = StdCommand::new("git")
        .args(["ls-remote", "--tags", &path_str(origin.path()), &tag_ref])
        .output()
        .unwrap();
    assert!(remote_listing.status.success());
    let remote_listing = String::from_utf8_lossy(&remote_listing.stdout);
    assert!(
        remote_listing.contains(candidate),
        "candidate tag did not reach origin: {remote_listing}"
    );
}

/// A reviewer who never accepted (or was never nominated at all) must be
/// refused outright -- `prepare-merge` must not construct or tag anything
/// on their behalf.
#[test]
fn prepare_merge_rejects_a_reviewer_who_never_accepted_the_nomination() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let (nomination, _previous_main, feature_commit) = nominated_and_accepted_review(repo.path());
    register(repo.path(), "mallory", "reviewer", "host3");

    bin()
        .current_dir(repo.path())
        .args([
            "prepare-merge",
            "--agent",
            "mallory",
            "--nomination",
            &nomination,
            "--reviewed-commit",
            &feature_commit,
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains(
            "only the accepting reviewer may prepare a merge",
        ));
}

/// `verify_authorship`'s falsifying path reached through the real CLI: a
/// `reviewed_commit` whose introduced content carries no `Agent-Bus-Agent`
/// trailer at all must be refused, not silently accepted as if authorship
/// were unconstrained.
#[test]
fn prepare_merge_rejects_a_reviewed_commit_missing_the_author_trailer() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "aiden", "reviewer", "host2");
    register(repo.path(), "zoe", "implementor", "host2");

    // A commit with no trailer, so it cannot be nominated/authored the
    // normal way -- built directly, then a nomination is submitted whose
    // own bookkeeping doesn't care what the branch actually contains.
    let previous_main = crate_rev_parse(repo.path(), "main");
    git(
        repo.path(),
        &["checkout", "--quiet", "--detach", &previous_main],
    );
    std::fs::write(repo.path().join("feature.txt"), "feature content\n").unwrap();
    git(repo.path(), &["add", "."]);
    git(
        repo.path(),
        &["commit", "-q", "-m", "add feature, no trailer"],
    );
    let feature_commit = crate_rev_parse(repo.path(), "HEAD");
    git(repo.path(), &["checkout", "--quiet", "main"]);

    let nominate_data = serde_json::json!({
        "authors": ["zoe"],
        "product_branch": "refs/heads/agent/zoe/feature",
        "reviewer": "aiden",
        "required_checks": ["build"],
        "review_scope": ["feature.txt"],
        "summary": "add feature",
        "target_branch": "refs/heads/main",
        "evidence": [],
    });
    submit(
        repo.path(),
        "zoe",
        "review.nominated",
        &nominate_data.to_string(),
        "nominate",
    );
    let coordinated = coordinate(repo.path(), "zoe", "host2", 0);
    let nomination = coordinated["published_events"][0]
        .as_str()
        .unwrap()
        .to_string();
    let accept_data = serde_json::json!({"nomination": nomination, "note": "ok"});
    run_json(bin().current_dir(repo.path()).args([
        "submit",
        "--agent",
        "aiden",
        "--kind",
        "review.nomination_accepted",
        "--data",
        &accept_data.to_string(),
        "--client-id",
        "accept",
        "--observes",
        &nomination,
    ]));
    coordinate(repo.path(), "aiden", "host2", 0);

    bin()
        .current_dir(repo.path())
        .args([
            "prepare-merge",
            "--agent",
            "aiden",
            "--nomination",
            &nomination,
            "--reviewed-commit",
            &feature_commit,
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("has no Agent-Bus-Agent trailer"));
}

/// A nomination that exists and names the right reviewer, but was never
/// accepted, must still be refused -- distinct from the "wrong reviewer
/// entirely" case above (`chain.current_request.reviewer != reviewer`):
/// this exercises `!chain.accepted()` specifically.
#[test]
fn prepare_merge_rejects_before_the_nomination_is_accepted() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "aiden", "reviewer", "host2");
    register(repo.path(), "zoe", "implementor", "host2");
    let (_previous_main, feature_commit) = commit_feature_with_trailer(repo.path(), "zoe");

    let nominate_data = serde_json::json!({
        "authors": ["zoe"],
        "product_branch": "refs/heads/agent/zoe/feature",
        "reviewer": "aiden",
        "required_checks": ["build"],
        "review_scope": ["feature.txt"],
        "summary": "add feature",
        "target_branch": "refs/heads/main",
        "evidence": [],
    });
    submit(
        repo.path(),
        "zoe",
        "review.nominated",
        &nominate_data.to_string(),
        "nominate",
    );
    let coordinated = coordinate(repo.path(), "zoe", "host2", 0);
    let nomination = coordinated["published_events"][0]
        .as_str()
        .unwrap()
        .to_string();
    // Deliberately no `review.nomination_accepted` here.

    bin()
        .current_dir(repo.path())
        .args([
            "prepare-merge",
            "--agent",
            "aiden",
            "--nomination",
            &nomination,
            "--reviewed-commit",
            &feature_commit,
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains(
            "only the accepting reviewer may prepare a merge",
        ));
}

/// A nomination id that names an unknown event entirely (never published at
/// all) must fail with a clear, nomination-specific message.
#[test]
fn prepare_merge_rejects_an_unknown_nomination() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "aiden", "reviewer", "host2");

    bin()
        .current_dir(repo.path())
        .args([
            "prepare-merge",
            "--agent",
            "aiden",
            "--nomination",
            "aiden:99",
            "--reviewed-commit",
            &"a".repeat(40),
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("unknown nomination"));
}

// `prepare_merge`'s `chain.current_nomination != nomination` branch
// ("nomination is no longer current") is deliberately left without a CLI-
// level test here. The only way to reach it is a confirmed `review.
// reassigned` moving the chain past an old nomination link, and `review.
// reassigned` is gate-17 currency-sensitive -- while investigating a test
// for exactly this, that fetch was found to trigger a real, separate,
// severe, pre-existing bug in this crate's local ref plumbing (see this
// task's final report): `stream.rs`/`registry.rs` update every local
// stream/registry ref via `git branch -f <already-fully-qualified-ref>`
// (e.g. `git branch -f refs/heads/agent-events/zoe <commit>`), which real
// `git` does not treat as already-qualified -- it creates `refs/heads/
// refs/heads/agent-events/zoe` instead (confirmed empirically). Every
// ordinary read still resolves correctly only by accident, via `git rev-
// parse`'s ref-disambiguation fallback chain finding the doubly-prefixed
// ref. But `sync::synced_snapshot`'s own fetch (gate 17's currency probe,
// or `--sync`) uses an explicit `<remote-ref>:<local-ref>` refspec that
// *does* create the correctly-named exact ref as a byproduct -- and once
// that exact ref exists, `rev-parse`'s disambiguation prefers it (its first
// rule is a literal path match) over the doubly-prefixed one *forever*,
// permanently shadowing that agent's real, advancing tip with whatever
// commit the remote happened to have at that one fetch moment. Reassigning
// as the same agent whose own reassignment is the currency-sensitive event
// hits this immediately: gate 17's fetch (for that very candidate) pins the
// exact ref to the pre-reassignment tip, the reassignment still commits
// onto the doubly-prefixed ref locally, but `publish_stream`'s own `read_
// stream_tip` afterward reads the now-shadowed, stale exact ref -- so the
// event is reported published (it *is* a real local commit) while the
// actual push silently reuses the old tip, never reaching the remote.
// Fixing this is real, separate work (`stream.rs`/`registry.rs`'s ref-
// update calls, used by every stream and the registry root, well outside
// this task's git-linked-review-checks scope) -- flagged, not fixed, here.

// ======================================================= merge-ready (gate 8)
//
// AGENT_REVIEW.md section 8: run immediately after publishing `review.
// merge_authorized` and immediately before pushing the candidate to `main`.
// `merge_ready_reports_ready_for_a_genuinely_valid_authorization` below is
// the one full end-to-end happy path in this suite that actually reaches a
// *published* `review.merge_authorized` (via `activate_merge_engine` --
// `prepare_merge`'s own tests document why they stop short of that).

/// The full, genuinely valid path: nominate, accept, activate the merge
/// engine, prepare the candidate, authorize it, then confirm `merge-ready`
/// reports it ready and names the exact same candidate.
#[test]
fn merge_ready_reports_ready_for_a_genuinely_valid_authorization() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let (nomination, previous_main, feature_commit) = nominated_and_accepted_review(repo.path());
    let merge_engine_epoch = activate_merge_engine(repo.path(), "coord1");

    let prepared = prepare_merge(repo.path(), "aiden", &nomination, &feature_commit);
    let candidate = prepared["candidate"].as_str().unwrap().to_string();

    let authorization_id = authorize_merge(
        repo.path(),
        "aiden",
        &nomination,
        &previous_main,
        &feature_commit,
        &candidate,
        &merge_engine_epoch,
        &["feature.txt"],
    );

    let out = merge_ready(repo.path(), "aiden", &authorization_id);
    assert_eq!(out["ready"], true, "{out}");
    assert_eq!(out["candidate"], candidate, "{out}");
}

#[test]
fn merge_ready_rejects_unknown_authorization() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "aiden", "reviewer", "host2");

    bin()
        .current_dir(repo.path())
        .args([
            "merge-ready",
            "--agent",
            "aiden",
            "--authorization",
            "aiden:99",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("unknown authorization"));
}

/// The authorizing reviewer was `aiden`; a different registered reviewer
/// asking `merge-ready` about the same authorization id must be refused.
#[test]
fn merge_ready_rejects_wrong_authorizer() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let (nomination, previous_main, feature_commit) = nominated_and_accepted_review(repo.path());
    let merge_engine_epoch = activate_merge_engine(repo.path(), "coord1");
    let prepared = prepare_merge(repo.path(), "aiden", &nomination, &feature_commit);
    let candidate = prepared["candidate"].as_str().unwrap().to_string();
    let authorization_id = authorize_merge(
        repo.path(),
        "aiden",
        &nomination,
        &previous_main,
        &feature_commit,
        &candidate,
        &merge_engine_epoch,
        &["feature.txt"],
    );
    register(repo.path(), "mallory", "reviewer", "host3");

    bin()
        .current_dir(repo.path())
        .args([
            "merge-ready",
            "--agent",
            "mallory",
            "--authorization",
            &authorization_id,
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains(
            "was not published by the given reviewer",
        ));
}

/// `main` moving out from under an already-published authorization is
/// exactly the time-sensitive scenario this whole gate exists to catch --
/// neither `apply_review_merge_authorized` (reduction time) nor `coordinator
/// ::verify_review_merge_authorized` (publication time) could ever observe
/// this, since both run before `main` has had the chance to move.
#[test]
fn merge_ready_rejects_main_advanced() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let (nomination, previous_main, feature_commit) = nominated_and_accepted_review(repo.path());
    let merge_engine_epoch = activate_merge_engine(repo.path(), "coord1");
    let prepared = prepare_merge(repo.path(), "aiden", &nomination, &feature_commit);
    let candidate = prepared["candidate"].as_str().unwrap().to_string();
    let authorization_id = authorize_merge(
        repo.path(),
        "aiden",
        &nomination,
        &previous_main,
        &feature_commit,
        &candidate,
        &merge_engine_epoch,
        &["feature.txt"],
    );

    // Advance `main` past `previous_main` out from under the authorization,
    // as a hand push (or a different, concurrently-merged reviewer) would.
    git(
        repo.path(),
        &["update-ref", "refs/heads/main", &feature_commit],
    );

    bin()
        .current_dir(repo.path())
        .args([
            "merge-ready",
            "--agent",
            "aiden",
            "--authorization",
            &authorization_id,
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains(
            "has advanced past authorized previous_main",
        ));
}

/// The reviewed commit touches sneaky.txt too, but review_scope/
/// reviewed_scope only ever name feature.txt -- `merge-ready`'s own diff
/// check is what must catch this (nothing upstream of it inspects changed
/// paths at all: neither `apply_review_merge_authorized` nor `prepare-merge`
/// ever looks at the actual diff content).
#[test]
fn merge_ready_rejects_a_changed_path_outside_reviewed_scope() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register(repo.path(), "aiden", "reviewer", "host2");
    register(repo.path(), "zoe", "implementor", "host2");

    let previous_main = crate_rev_parse(repo.path(), "main");
    git(
        repo.path(),
        &["checkout", "--quiet", "--detach", &previous_main],
    );
    std::fs::write(repo.path().join("feature.txt"), "feature content\n").unwrap();
    std::fs::write(repo.path().join("sneaky.txt"), "sneaky content\n").unwrap();
    git(repo.path(), &["add", "."]);
    git(
        repo.path(),
        &["commit", "-q", "-m", "add feature\n\nAgent-Bus-Agent: zoe"],
    );
    let feature_commit = crate_rev_parse(repo.path(), "HEAD");
    git(repo.path(), &["checkout", "--quiet", "main"]);

    let nominate_data = serde_json::json!({
        "authors": ["zoe"],
        "product_branch": "refs/heads/agent/zoe/feature",
        "reviewer": "aiden",
        "required_checks": ["build"],
        "review_scope": ["feature.txt"],
        "summary": "add feature",
        "target_branch": "refs/heads/main",
        "evidence": [],
    });
    submit(
        repo.path(),
        "zoe",
        "review.nominated",
        &nominate_data.to_string(),
        "nominate",
    );
    let coordinated = coordinate(repo.path(), "zoe", "host2", 0);
    let nomination = coordinated["published_events"][0]
        .as_str()
        .unwrap()
        .to_string();
    let accept_data = serde_json::json!({"nomination": nomination, "note": "ok"});
    run_json(bin().current_dir(repo.path()).args([
        "submit",
        "--agent",
        "aiden",
        "--kind",
        "review.nomination_accepted",
        "--data",
        &accept_data.to_string(),
        "--client-id",
        "accept",
        "--observes",
        &nomination,
    ]));
    coordinate(repo.path(), "aiden", "host2", 0);
    let merge_engine_epoch = activate_merge_engine(repo.path(), "coord1");

    let prepared = prepare_merge(repo.path(), "aiden", &nomination, &feature_commit);
    let candidate = prepared["candidate"].as_str().unwrap().to_string();
    // Authorized `reviewed_scope` matches the nomination's declared scope
    // exactly (["feature.txt"]) -- only the *actual* diff leaks sneaky.txt.
    let authorization_id = authorize_merge(
        repo.path(),
        "aiden",
        &nomination,
        &previous_main,
        &feature_commit,
        &candidate,
        &merge_engine_epoch,
        &["feature.txt"],
    );

    bin()
        .current_dir(repo.path())
        .args([
            "merge-ready",
            "--agent",
            "aiden",
            "--authorization",
            &authorization_id,
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("is outside reviewed_scope"));
}

// ================================================================ golden tests

// ================================================================ golden tests
//
// One snapshot per distinct JSON *shape*, not per test case above -- the
// field-level tests already pin exact values for the scenarios that matter.
// Non-deterministic content (git object hashes, RFC3339 timestamps, and the
// temp-dir-derived `outbox_path`) is redacted before comparison.

#[test]
fn golden_genesis_output() {
    let (_origin, repo) = fresh_bus();
    let out = genesis(repo.path(), "coord1", "host1");
    insta::assert_json_snapshot!(out, {
        ".registry_epoch" => insta::dynamic_redaction(redact_noise),
        ".stream_commit" => insta::dynamic_redaction(redact_noise),
        ".published.*" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_register_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let out = register(repo.path(), "bob", "reviewer", "host2");
    insta::assert_json_snapshot!(out, {
        ".registry_epoch" => insta::dynamic_redaction(redact_noise),
        ".published.*" => insta::dynamic_redaction(redact_noise),
        ".roster_epoch" => insta::dynamic_redaction(redact_noise),
        ".snapshot_receipt.*" => insta::dynamic_redaction(redact_noise),
        ".causal_frontier.*" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_submit_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let out = submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "golden-submit-1",
    );
    insta::assert_json_snapshot!(out, {
        ".outbox_path" => "[outbox_path]",
    });
}

#[test]
fn golden_coordinate_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "c1",
    );
    let out = coordinate(repo.path(), "coord1", "host1", 0);
    insta::assert_json_snapshot!(out, {
        ".published.*" => insta::dynamic_redaction(redact_noise),
        ".roster_epoch" => insta::dynamic_redaction(redact_noise),
        ".snapshot_receipt.*" => insta::dynamic_redaction(redact_noise),
        ".causal_frontier.*" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_tail_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let out = tail(repo.path(), "coord1");
    insta::assert_json_snapshot!(out, {
        ".events[].time" => insta::dynamic_redaction(redact_noise),
        ".events[].observed.roster_epoch" => insta::dynamic_redaction(redact_noise),
        ".roster_epoch" => insta::dynamic_redaction(redact_noise),
        ".snapshot_receipt.*" => insta::dynamic_redaction(redact_noise),
        ".causal_frontier.*" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_outbox_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    submit(
        repo.path(),
        "coord1",
        "agent.status",
        r#"{"status":"active","note":"hi"}"#,
        "c1",
    );
    let out = outbox(repo.path(), "coord1");
    insta::assert_json_snapshot!(out, {
        ".pending[].outbox_path" => "[outbox_path]",
        ".roster_epoch" => insta::dynamic_redaction(redact_noise),
        ".snapshot_receipt.*" => insta::dynamic_redaction(redact_noise),
        ".causal_frontier.*" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_status_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let out = status(repo.path(), false);
    insta::assert_json_snapshot!(out, {
        ".roster_epoch" => insta::dynamic_redaction(redact_noise),
        ".agents[].stream_tip" => insta::dynamic_redaction(redact_noise),
        ".snapshot_receipt.*" => insta::dynamic_redaction(redact_noise),
        ".causal_frontier.*" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_succeed_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    register_with(
        repo.path(),
        "alice",
        "implementor",
        "host-a",
        Some("alice-standby"),
    );
    let out = succeed(repo.path(), "alice-standby", "alice", "host-b");
    insta::assert_json_snapshot!(out, {
        ".registry_epoch" => insta::dynamic_redaction(redact_noise),
        ".registry_published.*" => insta::dynamic_redaction(redact_noise),
        ".stream_published.*" => insta::dynamic_redaction(redact_noise),
        ".roster_epoch" => insta::dynamic_redaction(redact_noise),
        ".snapshot_receipt.*" => insta::dynamic_redaction(redact_noise),
        ".causal_frontier.*" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_prepare_merge_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let (nomination, _previous_main, feature_commit) = nominated_and_accepted_review(repo.path());
    let out = prepare_merge(repo.path(), "aiden", &nomination, &feature_commit);
    insta::assert_json_snapshot!(out, {
        ".candidate" => insta::dynamic_redaction(redact_noise),
        ".previous_main" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn golden_merge_ready_output() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");
    let (nomination, previous_main, feature_commit) = nominated_and_accepted_review(repo.path());
    let merge_engine_epoch = activate_merge_engine(repo.path(), "coord1");
    let prepared = prepare_merge(repo.path(), "aiden", &nomination, &feature_commit);
    let candidate = prepared["candidate"].as_str().unwrap().to_string();
    let authorization_id = authorize_merge(
        repo.path(),
        "aiden",
        &nomination,
        &previous_main,
        &feature_commit,
        &candidate,
        &merge_engine_epoch,
        &["feature.txt"],
    );
    let out = merge_ready(repo.path(), "aiden", &authorization_id);
    insta::assert_json_snapshot!(out, {
        ".candidate" => insta::dynamic_redaction(redact_noise),
    });
}

#[test]
fn register_rejects_a_syntactically_invalid_role() {
    let (_origin, repo) = fresh_bus();
    genesis(repo.path(), "coord1", "host1");

    bin()
        .current_dir(repo.path())
        .args([
            "register",
            "--agent",
            "alice",
            "--display-name",
            "Alice",
            "--role",
            "wizard",
            "--purpose",
            "x",
            "--host",
            "host1",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("invalid role"));
}

/// `register` before any `genesis` has ever run must fail with a clear,
/// actionable message, not a confusing lower-level error (e.g. "no
/// registry root" surfacing as a raw git failure).
#[test]
fn register_before_genesis_fails_cleanly() {
    let origin = init_bare_origin();
    let repo = init_repo(origin.path());
    bin()
        .current_dir(repo.path())
        .args([
            "register",
            "--agent",
            "alice",
            "--display-name",
            "Alice",
            "--role",
            "implementor",
            "--purpose",
            "x",
            "--host",
            "host1",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("run `genesis` first"));
}

#[test]
fn succeed_before_genesis_fails_cleanly() {
    let origin = init_bare_origin();
    let repo = init_repo(origin.path());
    bin()
        .current_dir(repo.path())
        .args([
            "succeed",
            "--proposer",
            "alice",
            "--target",
            "bob",
            "--host",
            "host1",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("run `genesis` first"));
}
