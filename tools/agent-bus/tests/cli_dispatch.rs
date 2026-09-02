//! Exercises the `main.rs` dispatch table arms that `cli_flow.rs` doesn't
//! reach: lifecycle admin (status-set/resume/retire/schema-activate/
//! merge-engine-activate/status), plan/progress, the full issue/dependency/
//! handoff/review side-channel command surfaces, and sync. `cli_flow.rs`
//! already covers bootstrap-init, register, issue open/resolve, scope set,
//! review nominate/take/authorize/merged, prepare-merge, merge-ready,
//! audit-main, conflicts, tail, and validate, so this file deliberately
//! avoids repeating those.

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

fn stdout_of(assert: assert_cmd::assert::Assert) -> String {
    String::from_utf8_lossy(&assert.get_output().stdout).to_string()
}

#[test]
fn dispatch_table_coverage() {
    let repo = init_repo();
    let dir = repo.path();
    let root = git(dir, &["rev-parse", "HEAD"]);
    let some_hash = root.clone();

    bus(dir)
        .args([
            "bootstrap-init",
            "--coordinator",
            "coord1",
            "--product-review-from",
            &root,
        ])
        .assert()
        .success();

    for (agent, role) in [
        ("alice", "implementor"),
        ("bob", "reviewer"),
        ("carol", "implementor"),
        ("dan", "implementor"),
    ] {
        bus(dir)
            .args([
                "register",
                "--agent",
                agent,
                "--display-name",
                agent,
                "--role",
                role,
                "--purpose",
                "x",
            ])
            .assert()
            .success();
    }

    // ---- agent.status / agent.resumed / agent.retired ----
    bus(dir)
        .args([
            "status-set",
            "--agent",
            "alice",
            "--status",
            "blocked",
            "--note",
            "stuck",
        ])
        .assert()
        .success();
    bus(dir)
        .args([
            "status-set",
            "--agent",
            "alice",
            "--status",
            "done",
            "--note",
            "",
        ])
        .assert()
        .success();
    bus(dir)
        .args([
            "resume",
            "--agent",
            "alice",
            "--reason",
            "back",
            "--user-authority",
            "user",
        ])
        .assert()
        .success();
    bus(dir)
        .args([
            "retire",
            "--agent",
            "coord1",
            "--target",
            "dan",
            "--reason",
            "done",
            "--user-authority",
            "user",
        ])
        .assert()
        .success();

    // ---- schema.activated / merge_engine.activated ----
    bus(dir)
        .args([
            "schema-activate",
            "--agent",
            "coord1",
            "--version",
            "2",
            "--design-commit",
            &some_hash,
            "--helper-commit",
            &some_hash,
        ])
        .assert()
        .success();
    bus(dir)
        .args([
            "merge-engine-activate",
            "--agent",
            "coord1",
            "--previous-epoch",
            "coord1:0",
            "--merge-engine",
            "git-ort",
            "--merge-engine-version",
            "2.53.0",
            "--design-commit",
            &some_hash,
            "--helper-commit",
            &some_hash,
        ])
        .assert()
        .success();

    // ---- status query (json + text, all + single agent) ----
    bus(dir).args(["status", "--json"]).assert().success();
    bus(dir)
        .args(["status", "--agent", "alice"])
        .assert()
        .success();

    // ---- plan.set / progress.reported ----
    let plan = serde_json::json!({
        "summary": "ship it", "steps": [{"id": "s1", "state": "active", "text": "do the thing"}], "risks": [],
    });
    let plan_file = write_json(dir, "plan.json", &plan);
    bus(dir)
        .args(["plan", "set", "--agent", "alice", "--file", &plan_file])
        .assert()
        .success();

    let progress = serde_json::json!({"completed": [], "current": ["doing x"], "next": [], "blockers": [], "verification": []});
    let progress_file = write_json(dir, "progress.json", &progress);
    bus(dir)
        .args(["progress", "--agent", "alice", "--file", &progress_file])
        .assert()
        .success();

    // ---- issue.acknowledged / issue.rejected / issue.reassigned ----
    let issue_ack_payload = serde_json::json!({
        "issue_kind": "question", "severity": "low", "summary": "q1",
        "locations": [], "reproduction": [], "blocks": [], "evidence": [],
    });
    let issue_ack_file = write_json(dir, "issue_ack.json", &issue_ack_payload);
    bus(dir)
        .args([
            "issue",
            "open",
            "--agent",
            "bob",
            "--to",
            "alice",
            "--file",
            &issue_ack_file,
        ])
        .assert()
        .success();
    let issue_ack_out = stdout_of(
        bus(dir)
            .args(["inbox", "--agent", "alice", "--json"])
            .assert()
            .success(),
    );
    let issue_ack_id = serde_json::from_str::<serde_json::Value>(&issue_ack_out).unwrap()[0]["id"]
        .as_str()
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "issue",
            "acknowledge",
            "--agent",
            "alice",
            &issue_ack_id,
            "--note",
            "on it",
        ])
        .assert()
        .success();

    let issue_rej_file = write_json(dir, "issue_rej.json", &issue_ack_payload);
    bus(dir)
        .args([
            "issue",
            "open",
            "--agent",
            "bob",
            "--to",
            "alice",
            "--file",
            &issue_rej_file,
        ])
        .assert()
        .success();
    let inbox = stdout_of(
        bus(dir)
            .args(["inbox", "--agent", "alice", "--json"])
            .assert()
            .success(),
    );
    let inbox_items: serde_json::Value = serde_json::from_str(&inbox).unwrap();
    let issue_rej_id = inbox_items
        .as_array()
        .unwrap()
        .iter()
        .find(|i| i["kind"] == "issue" && i["id"] != issue_ack_id)
        .expect("a second open issue")["id"]
        .as_str()
        .unwrap()
        .to_string();
    let reject_payload = serde_json::json!({"reason": "not reproducible", "normative_refs": []});
    let reject_file = write_json(dir, "issue_reject_payload.json", &reject_payload);
    bus(dir)
        .args([
            "issue",
            "reject",
            "--agent",
            "alice",
            &issue_rej_id,
            "--file",
            &reject_file,
        ])
        .assert()
        .success();

    let issue_reassign_file = write_json(dir, "issue_reassign.json", &issue_ack_payload);
    bus(dir)
        .args([
            "issue",
            "open",
            "--agent",
            "bob",
            "--to",
            "alice",
            "--file",
            &issue_reassign_file,
        ])
        .assert()
        .success();
    let inbox = stdout_of(
        bus(dir)
            .args(["inbox", "--agent", "alice", "--json"])
            .assert()
            .success(),
    );
    let inbox_items: serde_json::Value = serde_json::from_str(&inbox).unwrap();
    let issue_reassign_id = inbox_items
        .as_array()
        .unwrap()
        .iter()
        .find(|i| i["kind"] == "issue")
        .expect("an open issue")["id"]
        .as_str()
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "issue",
            "reassign",
            "--agent",
            "bob",
            &issue_reassign_id,
            "--new-target",
            "carol",
            "--reason",
            "reassigning",
        ])
        .assert()
        .success();

    // ---- dependency.* (request/acknowledge/resolve, then reject, then reassign) ----
    let dep_payload = serde_json::json!({
        "interface": "api-v1", "needed_by": "asap", "blocking": false, "summary": "need the endpoint", "evidence": [],
    });
    let dep_file = write_json(dir, "dep1.json", &dep_payload);
    let dep_open_out = stdout_of(
        bus(dir)
            .args([
                "dependency",
                "request",
                "--agent",
                "alice",
                "--to",
                "bob",
                "--file",
                &dep_file,
            ])
            .assert()
            .success(),
    );
    let dep_id = dep_open_out
        .trim()
        .strip_prefix("opened ")
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "dependency",
            "acknowledge",
            "--agent",
            "bob",
            &dep_id,
            "--note",
            "on it",
        ])
        .assert()
        .success();
    let dep_resolve_payload = serde_json::json!({"summary": "shipped", "verification": []});
    let dep_resolve_file = write_json(dir, "dep1_resolve.json", &dep_resolve_payload);
    bus(dir)
        .args([
            "dependency",
            "resolve",
            "--agent",
            "bob",
            &dep_id,
            "--file",
            &dep_resolve_file,
        ])
        .assert()
        .success();

    let dep2_file = write_json(dir, "dep2.json", &dep_payload);
    let dep2_open_out = stdout_of(
        bus(dir)
            .args([
                "dependency",
                "request",
                "--agent",
                "alice",
                "--to",
                "bob",
                "--file",
                &dep2_file,
            ])
            .assert()
            .success(),
    );
    let dep2_id = dep2_open_out
        .trim()
        .strip_prefix("opened ")
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "dependency",
            "reject",
            "--agent",
            "bob",
            &dep2_id,
            "--reason",
            "not needed",
        ])
        .assert()
        .success();

    let dep3_file = write_json(dir, "dep3.json", &dep_payload);
    let dep3_open_out = stdout_of(
        bus(dir)
            .args([
                "dependency",
                "request",
                "--agent",
                "alice",
                "--to",
                "bob",
                "--file",
                &dep3_file,
            ])
            .assert()
            .success(),
    );
    let dep3_id = dep3_open_out
        .trim()
        .strip_prefix("opened ")
        .unwrap()
        .to_string();
    // Dependency reassignment authority is the requester (alice), unlike
    // issue reassignment which is keyed off the opener of the issue itself —
    // for a dependency alice is both.
    bus(dir)
        .args([
            "dependency",
            "reassign",
            "--agent",
            "alice",
            &dep3_id,
            "--new-target",
            "carol",
            "--reason",
            "wrong owner",
        ])
        .assert()
        .success();

    // ---- dependencies query ----
    bus(dir)
        .args(["dependencies", "--agent", "alice", "--json"])
        .assert()
        .success();
    bus(dir)
        .args(["dependencies", "--agent", "bob"])
        .assert()
        .success();

    // ---- handoff.* (offer/accept, offer/decline, offer/withdraw) ----
    let feature_branch = "refs/heads/agent/alice/handoff-feature";
    let handoff_payload = serde_json::json!({
        "receiver": "bob", "scope": ["README.md"], "product_branch": feature_branch,
        "product_commit": root, "verification": [], "known_issues": [], "evidence": [], "summary": "handing off",
    });
    let handoff1_file = write_json(dir, "handoff1.json", &handoff_payload);
    let handoff1_out = stdout_of(
        bus(dir)
            .args([
                "handoff",
                "offer",
                "--agent",
                "alice",
                "--file",
                &handoff1_file,
            ])
            .assert()
            .success(),
    );
    let handoff1_id = handoff1_out
        .trim()
        .strip_prefix("offered ")
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "handoff",
            "accept",
            "--agent",
            "bob",
            &handoff1_id,
            "--note",
            "got it",
        ])
        .assert()
        .success();

    let handoff2_file = write_json(dir, "handoff2.json", &handoff_payload);
    let handoff2_out = stdout_of(
        bus(dir)
            .args([
                "handoff",
                "offer",
                "--agent",
                "alice",
                "--file",
                &handoff2_file,
            ])
            .assert()
            .success(),
    );
    let handoff2_id = handoff2_out
        .trim()
        .strip_prefix("offered ")
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "handoff",
            "decline",
            "--agent",
            "bob",
            &handoff2_id,
            "--reason",
            "not ready",
        ])
        .assert()
        .success();

    let handoff3_file = write_json(dir, "handoff3.json", &handoff_payload);
    let handoff3_out = stdout_of(
        bus(dir)
            .args([
                "handoff",
                "offer",
                "--agent",
                "alice",
                "--file",
                &handoff3_file,
            ])
            .assert()
            .success(),
    );
    let handoff3_id = handoff3_out
        .trim()
        .strip_prefix("offered ")
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "handoff",
            "withdraw",
            "--agent",
            "alice",
            &handoff3_id,
            "--reason",
            "changed mind",
        ])
        .assert()
        .success();

    // ---- review.nomination_declined / review.withdrawn ----
    let base = git(dir, &["rev-parse", "main"]);
    let scope = serde_json::json!({
        "base_code_commit": base, "exclusive": ["dispatch.txt"], "shared": [], "exports": [], "depends_on": [], "note": "n",
    });
    let scope_file = write_json(dir, "scope.json", &scope);
    bus(dir)
        .args(["scope", "set", "--agent", "alice", "--file", &scope_file])
        .assert()
        .success();

    git(dir, &["checkout", "-b", "agent/alice/dispatch", "main"]);
    std::fs::write(dir.join("dispatch.txt"), "content\n").unwrap();
    git(dir, &["add", "dispatch.txt"]);
    git(
        dir,
        &[
            "commit",
            "-q",
            "-m",
            "add dispatch.txt\n\nAgent-Bus-Agent: alice",
        ],
    );
    git(dir, &["checkout", "main"]);

    let nom_payload = serde_json::json!({
        "authors": ["alice"], "product_branch": "refs/heads/agent/alice/dispatch", "reviewer": "bob",
        "required_checks": [], "review_scope": ["dispatch.txt"], "summary": "n1",
        "target_branch": "refs/heads/main", "evidence": [],
    });
    let nom1_file = write_json(dir, "nom1.json", &nom_payload);
    let nom1_out = stdout_of(
        bus(dir)
            .args([
                "review", "nominate", "--agent", "alice", "--file", &nom1_file,
            ])
            .assert()
            .success(),
    );
    let nom1_id = nom1_out
        .trim()
        .strip_prefix("nominated ")
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "review", "decline", "--agent", "bob", &nom1_id, "--reason", "too busy",
        ])
        .assert()
        .success();

    let nom2_file = write_json(dir, "nom2.json", &nom_payload);
    let nom2_out = stdout_of(
        bus(dir)
            .args([
                "review", "nominate", "--agent", "alice", "--file", &nom2_file,
            ])
            .assert()
            .success(),
    );
    let nom2_id = nom2_out
        .trim()
        .strip_prefix("nominated ")
        .unwrap()
        .to_string();
    bus(dir)
        .args([
            "review",
            "withdraw",
            "--agent",
            "alice",
            &nom2_id,
            "--reason",
            "changed mind",
        ])
        .assert()
        .success();

    // ---- sync ----
    bus(dir)
        .args(["sync", "--agent", "alice"])
        .assert()
        .success();

    bus(dir).arg("validate").assert().success();
}
