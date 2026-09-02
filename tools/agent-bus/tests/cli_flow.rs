//! End-to-end CLI tests against real throwaway git repositories, covering the
//! full bootstrap -> register -> scope -> review -> merge -> audit pipeline
//! (AGENT_BUS.md / AGENT_REVIEW.md) plus a couple of negative cases.

use assert_cmd::Command;
use std::path::Path;
use std::process::Command as StdCommand;

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
    StdCommand::new("git").args(["init", "--quiet", "-b", "main"]).arg(path).status().unwrap();
    git(path, &["config", "user.email", "test@example.com"]);
    git(path, &["config", "user.name", "Test"]);
    std::fs::write(path.join("README.md"), "hello\n").unwrap();
    git(path, &["add", "README.md"]);
    git(path, &["commit", "-q", "-m", "initial"]);
    dir
}

fn bus(dir: &Path) -> Command {
    let mut cmd = Command::cargo_bin("agent-bus").unwrap();
    cmd.arg("--repo").arg(dir);
    cmd
}

fn write_json(dir: &Path, name: &str, value: &serde_json::Value) -> String {
    let path = dir.join(name);
    std::fs::write(&path, serde_json::to_vec(value).unwrap()).unwrap();
    path.to_string_lossy().to_string()
}

#[test]
fn full_review_merge_and_audit_flow() {
    let repo = init_repo();
    let dir = repo.path();
    let root = git(dir, &["rev-parse", "HEAD"]);

    bus(dir)
        .args(["bootstrap-init", "--coordinator", "coord1", "--product-review-from", &root])
        .assert()
        .success();

    bus(dir)
        .args([
            "register", "--agent", "alice", "--display-name", "Alice",
            "--role", "implementor", "--purpose", "does stuff",
        ])
        .assert()
        .success();
    bus(dir)
        .args([
            "register", "--agent", "bob", "--display-name", "Bob",
            "--role", "reviewer", "--purpose", "reviews stuff",
        ])
        .assert()
        .success();

    // Double registration must fail.
    bus(dir)
        .args([
            "register", "--agent", "alice", "--display-name", "Alice2",
            "--role", "implementor", "--purpose", "dup",
        ])
        .assert()
        .failure();

    // A reference to a nonexistent event must be rejected before publishing
    // anything (no garbage event should land in bob's log).
    bus(dir)
        .args(["review", "take", "--agent", "bob", "alice:99"])
        .assert()
        .failure();
    let bob_log = bus(dir).args(["tail", "--agent", "bob"]).output().unwrap();
    let bob_log = String::from_utf8_lossy(&bob_log.stdout);
    assert_eq!(bob_log.lines().count(), 1, "only the registration should be present: {bob_log}");

    git(dir, &["checkout", "-b", "agent/alice/feature", "main"]);
    std::fs::write(dir.join("feature.txt"), "feature content\n").unwrap();
    git(dir, &["add", "feature.txt"]);
    git(dir, &["commit", "-q", "-m", "add feature\n\nAgent-Bus-Agent: alice"]);
    let feature = git(dir, &["rev-parse", "HEAD"]);
    git(dir, &["checkout", "main"]);

    let scope = serde_json::json!({
        "base_code_commit": git(dir, &["rev-parse", "main"]),
        "exclusive": ["feature.txt"], "shared": [], "exports": [], "depends_on": [], "note": "feature scope",
    });
    let scope_file = write_json(dir, "scope.json", &scope);
    bus(dir).args(["scope", "set", "--agent", "alice", "--file", &scope_file]).assert().success();

    let nom = serde_json::json!({
        "authors": ["alice"], "product_branch": "refs/heads/agent/alice/feature", "reviewer": "bob",
        "required_checks": ["build"], "review_scope": ["feature.txt"], "summary": "add feature",
        "target_branch": "refs/heads/main", "evidence": [],
    });
    let nom_file = write_json(dir, "nom.json", &nom);
    bus(dir).args(["review", "nominate", "--agent", "alice", "--file", &nom_file]).assert().success();
    // alice:0 register, alice:1 scope, alice:2 nominate
    let nomination_id = "alice:2";

    bus(dir).args(["review", "take", "--agent", "bob", nomination_id]).assert().success();

    let prepare_out = bus(dir)
        .args(["prepare-merge", "--agent", "bob", "--nomination", nomination_id, "--reviewed-commit", &feature])
        .output()
        .unwrap();
    assert!(prepare_out.status.success(), "{}", String::from_utf8_lossy(&prepare_out.stderr));
    let stdout = String::from_utf8_lossy(&prepare_out.stdout);
    let candidate = stdout
        .lines()
        .find_map(|l| l.strip_prefix("candidate "))
        .expect("candidate line")
        .to_string();
    let previous_main = stdout
        .lines()
        .find_map(|l| l.strip_prefix("previous_main "))
        .expect("previous_main line")
        .to_string();
    let merge_engine_epoch = stdout
        .lines()
        .find_map(|l| l.strip_prefix("merge_engine_epoch "))
        .expect("merge_engine_epoch line")
        .to_string();

    let auth = serde_json::json!({
        "nomination": nomination_id, "product_branch": "refs/heads/agent/alice/feature",
        "previous_main": previous_main, "reviewed_commit": feature, "candidate": candidate,
        "merge_engine_epoch": merge_engine_epoch,
        "checks": [{"command": "build", "result": "passed"}], "finding_dispositions": [],
        "evidence": [], "reviewed_scope": ["feature.txt"], "limitations": [], "summary": "looks good",
    });
    let auth_file = write_json(dir, "auth.json", &auth);
    bus(dir).args(["review", "authorize", "--agent", "bob", "--file", &auth_file]).assert().success();
    // bob:0 register, bob:1 take, bob:2 authorize
    let authorization_id = "bob:2";

    bus(dir)
        .args(["merge-ready", "--agent", "bob", "--authorization", authorization_id])
        .assert()
        .success();

    // Simulate the reviewer's non-force push of the candidate onto main
    // (a real push is refused here only because this repo's `main` happens
    // to be checked out in the same working tree; that's a local-fixture
    // artifact of the test, not part of the protocol).
    git(dir, &["update-ref", "refs/heads/main", &candidate]);

    let merged = serde_json::json!({
        "authorization": authorization_id, "previous_main": previous_main, "main_commit": candidate,
        "product_branch": "refs/heads/agent/alice/feature", "reviewed_commit": feature, "summary": "merged",
    });
    let merged_file = write_json(dir, "merged.json", &merged);
    bus(dir).args(["review", "merged", "--agent", "bob", "--file", &merged_file]).assert().success();

    let audit = bus(dir).args(["audit-main", "--json"]).output().unwrap();
    assert!(audit.status.success());
    let findings: serde_json::Value = serde_json::from_slice(&audit.stdout).unwrap();
    assert_eq!(findings.as_array().unwrap().len(), 0, "audit-main should be clean: {findings}");

    bus(dir).arg("validate").assert().success();

    // A legitimately-authorized-and-merged candidate must pass `--linked`'s
    // independent tag/parents/trailer/reconstruction checks cleanly.
    let linked = bus(dir).args(["validate", "--linked", "--json"]).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let linked: serde_json::Value = serde_json::from_slice(&linked.stdout).unwrap();
    assert_eq!(
        linked["linked"]["invalid"].as_array().unwrap().len(),
        0,
        "linked validation should find no invalid items: {linked}"
    );
    assert_eq!(
        linked["linked"]["unverifiable"].as_array().unwrap().len(),
        0,
        "linked validation should find no unverifiable items: {linked}"
    );
}

#[test]
fn issue_lifecycle_and_scope_conflicts() {
    let repo = init_repo();
    let dir = repo.path();
    let root = git(dir, &["rev-parse", "HEAD"]);

    bus(dir)
        .args(["bootstrap-init", "--coordinator", "coord1", "--product-review-from", &root])
        .assert()
        .success();
    for (agent, role) in [("alice", "implementor"), ("bob", "implementor")] {
        bus(dir)
            .args(["register", "--agent", agent, "--display-name", agent, "--role", role, "--purpose", "x"])
            .assert()
            .success();
    }

    let issue = serde_json::json!({
        "issue_kind": "bug", "severity": "high", "summary": "off by one",
        "locations": ["feature.txt:1"], "reproduction": [], "blocks": [], "evidence": [],
    });
    let issue_file = write_json(dir, "issue.json", &issue);
    bus(dir).args(["issue", "open", "--agent", "bob", "--to", "alice", "--file", &issue_file]).assert().success();
    // bob:0 register, bob:1 issue open
    let issue_id = "bob:1";

    let inbox = bus(dir).args(["inbox", "--agent", "alice", "--json"]).output().unwrap();
    let inbox: serde_json::Value = serde_json::from_slice(&inbox.stdout).unwrap();
    assert_eq!(inbox.as_array().unwrap().len(), 1);

    let resolve = serde_json::json!({"summary": "fixed", "verification": ["build"]});
    let resolve_file = write_json(dir, "resolve.json", &resolve);
    bus(dir).args(["issue", "resolve", "--agent", "alice", issue_id, "--file", &resolve_file]).assert().success();

    let inbox_after = bus(dir).args(["inbox", "--agent", "alice", "--json"]).output().unwrap();
    let inbox_after: serde_json::Value = serde_json::from_slice(&inbox_after.stdout).unwrap();
    assert_eq!(inbox_after.as_array().unwrap().len(), 0);

    // Overlapping exclusive scope claims should surface as a conflict.
    let base = git(dir, &["rev-parse", "main"]);
    let scope_a = serde_json::json!({
        "base_code_commit": base, "exclusive": ["shared/dir/**"], "shared": [],
        "exports": [], "depends_on": [], "note": "a",
    });
    let scope_b = serde_json::json!({
        "base_code_commit": base, "exclusive": ["shared/dir/file.txt"], "shared": [],
        "exports": [], "depends_on": [], "note": "b",
    });
    let sa = write_json(dir, "scope_a.json", &scope_a);
    let sb = write_json(dir, "scope_b.json", &scope_b);
    bus(dir).args(["scope", "set", "--agent", "alice", "--file", &sa]).assert().success();
    bus(dir).args(["scope", "set", "--agent", "bob", "--file", &sb]).assert().success();

    let conflicts = bus(dir).args(["conflicts", "--json"]).output().unwrap();
    let conflicts: serde_json::Value = serde_json::from_slice(&conflicts.stdout).unwrap();
    assert!(
        conflicts.as_array().unwrap().iter().any(|c| c["kind"] == "scope"),
        "expected a scope conflict: {conflicts}"
    );

    bus(dir).arg("validate").assert().success();
}
