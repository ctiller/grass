//! AGENT_REVIEW.md sections 9/11/12 (fixture 10): `audit-main` is the
//! read-only correlation-and-report half of the review/merge protocol's
//! detection story -- "A missing or mismatched receipt is detected by
//! `audit-main` and blocks that reviewer from taking more work until
//! repaired" (section 1), and "`agent-bus audit-main` detects bypasses by
//! correlating every post-bootstrap first-parent merge with its
//! authorization and receipt" (section 9). Unlike `merge_ready` (a
//! *pre*-push gate run once, by the reviewer, immediately before pushing one
//! specific candidate), this walks the *entire* post-bootstrap `main`
//! history and reports every commit that does not correlate cleanly with a
//! real `review.merge_authorized`/`review.merged`-or-`review.merge_
//! reconciled` chain -- the only mechanism that can ever catch a hand-pushed
//! or otherwise out-of-protocol commit *after* it has already landed, since
//! nothing upstream of `main` itself can refuse a push performed outside
//! this helper (section 9: "this is deliberately cooperative, not a claim
//! that a local helper can reject a direct push performed outside it").
//!
//! Ported closely from the shipped version-one helper's `review_cmds::
//! audit_main`/`audit_main_findings` (see its own `audit_main_flags_*` test
//! list) onto v2's `BusState`/`sync::Snapshot` primitives -- only the
//! agent/collection types and the source of `product_review_from` differ
//! (v1 read it off `BusCtx::bus_json()`; v2 carries it directly on `BusState::
//! config`, already loaded by every caller). `cli::audit_main` is the thin
//! CLI wrapper (arg parsing, snapshot load, plain-or-JSON output) around
//! [`audit_main_findings`] below, mirroring `cli::merge_ready`'s wrapper
//! around `merge_ready::check_merge_ready`.
//!
//! Known, accepted gap (carried forward verbatim from v1): a commit that
//! landed on `main` through ordinary git *before* this protocol was ever
//! wired up in a given repository (i.e. between `bootstrap-init`'s `product_
//! review_from` and that repository's first real review-authorized
//! candidate) will not be shaped as a two-parent review-candidate merge, and
//! `audit-main` will flag it as such. This is a one-time adoption artifact,
//! not a code defect: `main`'s history prior to actual agent-bus adoption
//! cannot retroactively become protocol-compliant. Treat any `audit-main`
//! finding whose commit predates a repository's first successful `review.
//! merged`/`review.merge_reconciled` receipt as this known bootstrap gap
//! rather than a live regression.

use crate::error::{invalid, AbResult};
use crate::events::{EventData, Role};
use crate::scalars::Agent;
use crate::state::BusState;
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::Path;

/// Every commit introduced by `reviewed_commit` over `previous_main`,
/// requiring each to carry at least one `Agent-Bus-Agent` trailer. Distinct
/// from (and deliberately not sharing code with) `merge_candidate::verify_
/// authorship`: that function additionally *rejects* a reviewer-authored
/// commit and an author-set mismatch against a *claimed* nomination outright
/// (the right behavior for a live gate deciding whether to accept a
/// publication); this one only collects who actually authored what, so the
/// caller can compare that against a chain's *real* recorded authors as one
/// of several independent findings -- mirrors v1's own separate `review_
/// cmds::commit_authors_only`, which existed for the identical reason.
fn commit_authors_only(
    repo: &Path,
    previous_main: &str,
    reviewed_commit: &str,
) -> AbResult<BTreeSet<Agent>> {
    let introduced = crate::gitrepo::commits_between_first_parent_exclusive(
        repo,
        previous_main,
        reviewed_commit,
    )?;
    let mut authors = BTreeSet::new();
    for c in &introduced {
        let trailers = crate::gitrepo::commit_message_trailers(repo, c)?;
        let mut commit_authors = BTreeSet::new();
        for (k, v) in trailers {
            if k == "Agent-Bus-Agent" {
                commit_authors.insert(Agent::parse(v)?);
            }
        }
        if commit_authors.is_empty() {
            return Err(invalid(format!(
                "commit {c} has no Agent-Bus-Agent trailer"
            )));
        }
        authors.extend(commit_authors);
    }
    Ok(authors)
}

/// The pure correlation walk behind `cli::audit_main`. Walks post-bootstrap
/// first-parent `main` history (`state.config.product_review_from` exclusive
/// through `to`, default `refs/heads/main`) and, for each commit, checks in
/// order: it is a genuine two-parent merge whose first parent is the prior
/// audited commit; it carries exactly one `Agent-Bus-Reviewer` trailer
/// naming a real, currently-a-reviewer identity; the reviewer authored none
/// of the commits the merge actually introduces; a `review.merge_authorized`
/// event exists whose recorded `candidate`/`previous_main`/`reviewed_commit`
/// *exactly* match this real commit (not merely "some authorization exists
/// for a nomination with plausible authors/reviewer" -- see the near-miss
/// case this guards against in the test suite); and a `review.merged` or
/// `review.merge_reconciled` receipt exists naming this exact commit as
/// `main_commit`. Each independent problem for a commit is reported as its
/// own finding rather than stopping at the first; a structurally broken
/// commit (not a two-parent merge, or a missing/duplicate reviewer trailer,
/// or an author-trailer failure) short-circuits the remaining checks for
/// *that* commit only, since they have nothing meaningful left to check.
pub(crate) fn audit_main_findings(
    repo: &Path,
    state: &BusState,
    to: Option<&str>,
) -> AbResult<Vec<Value>> {
    let to = to.unwrap_or("refs/heads/main");
    let commits =
        crate::gitrepo::rev_list_first_parent(repo, state.config.product_review_from.as_str(), to)?;

    let mut findings = Vec::new();
    let mut previous = state.config.product_review_from.as_str().to_string();
    for commit in commits {
        let parents = crate::gitrepo::parents_of(repo, &commit)?;
        if parents.len() != 2 || parents[0] != previous {
            findings.push(serde_json::json!({
                "commit": commit,
                "problem": "not a two-parent merge whose first parent is the prior audited main commit",
            }));
            previous = commit;
            continue;
        }
        let reviewed_commit = parents[1].clone();

        let trailers = crate::gitrepo::commit_message_trailers(repo, &commit)?;
        let reviewer_trailers: Vec<&(String, String)> = trailers
            .iter()
            .filter(|(k, _)| k == "Agent-Bus-Reviewer")
            .collect();
        if reviewer_trailers.len() != 1 {
            findings.push(serde_json::json!({
                "commit": commit,
                "problem": "missing or duplicate Agent-Bus-Reviewer trailer",
            }));
            previous = commit;
            continue;
        }
        let reviewer_name = reviewer_trailers[0].1.clone();
        let reviewer = match Agent::parse(reviewer_name.clone()) {
            Ok(a) => a,
            Err(_) => {
                findings.push(serde_json::json!({
                    "commit": commit,
                    "problem": "Agent-Bus-Reviewer trailer is not a valid agent name",
                }));
                previous = commit;
                continue;
            }
        };
        if state.agents.get(&reviewer).map(|a| a.primary_role) != Some(Role::Reviewer) {
            findings.push(serde_json::json!({
                "commit": commit,
                "problem": "trailer names a non-reviewer identity",
                "reviewer": reviewer_name,
            }));
        }

        let introduced_authors = match commit_authors_only(repo, &previous, &reviewed_commit) {
            Ok(a) => a,
            Err(e) => {
                findings.push(serde_json::json!({
                    "commit": commit,
                    "problem": format!("author trailer check failed: {e}"),
                }));
                previous = commit;
                continue;
            }
        };
        if introduced_authors.contains(&reviewer) {
            findings.push(serde_json::json!({
                "commit": commit,
                "problem": "reviewer authored an introduced commit",
                "reviewer": reviewer_name,
            }));
        }

        let matching_auth = state.reviews.values().find(|chain| {
            let authors_match = introduced_authors
                == chain
                    .current_request
                    .authors
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<Agent>>();
            authors_match
                && chain.authorizations.iter().any(|a| {
                    a.agent() == reviewer
                        && state
                            .events
                            .get(a)
                            .and_then(|e| e.typed_data().ok())
                            .map(|d| match d {
                                EventData::ReviewMergeAuthorized(auth) => {
                                    auth.candidate.as_str() == commit
                                        && auth.previous_main.as_str() == previous
                                        && auth.reviewed_commit.as_str() == reviewed_commit
                                }
                                _ => false,
                            })
                            .unwrap_or(false)
                })
        });
        match matching_auth {
            None => {
                findings.push(serde_json::json!({
                    "commit": commit,
                    "problem": "no review.merge_authorized matches this exact candidate/previous_main/reviewed_commit",
                    "reviewer": reviewer_name,
                }));
            }
            Some(chain) => {
                let has_receipt = chain.merged.iter().chain(chain.reconciled.iter()).any(|r| {
                    state
                        .events
                        .get(r)
                        .and_then(|e| e.typed_data().ok())
                        .map(|d| match d {
                            EventData::ReviewMerged(m) => m.main_commit.as_str() == commit,
                            EventData::ReviewMergeReconciled(m) => m.main_commit.as_str() == commit,
                            _ => false,
                        })
                        .unwrap_or(false)
                });
                if !has_receipt {
                    findings.push(serde_json::json!({
                        "commit": commit,
                        "problem": "missing review.merged/review.merge_reconciled receipt for this exact commit",
                        "reviewer": reviewer_name,
                    }));
                }
            }
        }
        previous = commit;
    }

    Ok(findings)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bootstrap::BusConfig;
    use crate::envelope::Envelope;
    use crate::events::{
        AgentRegistered, ReviewMergeAuthorized, ReviewMergeReconciled, ReviewMerged,
        ReviewNominated,
    };
    use crate::frontier::ObservedFrontier;
    use crate::scalars::{Branch, EventId, ObjectId, Short, StringSet, Text};
    use crate::state::{ItemStatus, ReviewChain};
    use std::collections::BTreeMap;
    use std::path::Path;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> Text {
        Text::parse(s.to_string()).unwrap()
    }

    fn oid(s: &str) -> ObjectId {
        ObjectId::parse(s.to_string()).unwrap()
    }

    fn no_frontier(root: &str) -> ObservedFrontier {
        ObservedFrontier::sparse(oid(root), [])
    }

    // ------------------------------------------------------------- git setup

    fn git(dir: &Path, args: &[&str]) -> String {
        let out = std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .output()
            .unwrap();
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
        git(path, &["init", "--quiet", "-b", "main"]);
        git(path, &["config", "user.email", "test@example.com"]);
        git(path, &["config", "user.name", "Test"]);
        std::fs::write(path.join("README.md"), "hello\n").unwrap();
        git(path, &["add", "README.md"]);
        git(path, &["commit", "-q", "-m", "initial"]);
        dir
    }

    /// A commit on top of `base` touching `file`, carrying `Agent-Bus-Agent:
    /// <trailer_agent>` -- or no trailer at all when `trailer_agent` is
    /// `None`, for the "missing author trailer" fixture.
    fn author_commit(path: &Path, base: &str, file: &str, trailer_agent: Option<&str>) -> String {
        git(path, &["checkout", "--quiet", "--detach", base]);
        std::fs::write(path.join(file), "content\n").unwrap();
        git(path, &["add", file]);
        let message = match trailer_agent {
            Some(ag) => format!("add {file}\n\nAgent-Bus-Agent: {ag}"),
            None => format!("add {file}"),
        };
        git(path, &["commit", "-q", "-m", &message]);
        let commit = git(path, &["rev-parse", "HEAD"]);
        git(path, &["checkout", "--quiet", "main"]);
        commit
    }

    fn merge_commit(path: &Path, first_parent: &str, second_parent: &str, message: &str) -> String {
        let tree = git(path, &["rev-parse", &format!("{second_parent}^{{tree}}")]);
        git(
            path,
            &[
                "commit-tree",
                &tree,
                "-p",
                first_parent,
                "-p",
                second_parent,
                "-m",
                message,
            ],
        )
    }

    // ------------------------------------------------------------ bus setup

    fn config(root: &str) -> BusConfig {
        BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: oid(root),
            merge_engine: crate::bootstrap::SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
        }
    }

    /// A `BusState` with `alice` (implementor) and `bob` (reviewer)
    /// registered via the real `agent.registered` reduction path
    /// (`apply::reduce_onto`) -- so `state.agents` is populated exactly as
    /// production code would produce it, not hand-assembled -- and nothing
    /// else. Individual tests attach their own `ReviewChain`/authorization/
    /// receipt events directly (like `merge_ready.rs`'s own fixtures: see
    /// that module's `fixture`/`state_with_authorization` doc comments for
    /// why hand-building those specifically, rather than running them
    /// through `apply_event`, is the right choice here -- `audit_main_
    /// findings` is a read-only correlation walk over whatever `state`
    /// already contains, and several of the cases below (no authorization at
    /// all, an authorization for a different exact commit, a chain with no
    /// receipt) are exactly the "state audit-main must survive even though
    /// production reduction would rarely produce it this way" shapes).
    fn base_state(root: &str) -> BusState {
        let state = BusState::new(config(root));
        let alice_env = Envelope::new(
            &a("alice"),
            0,
            no_frontier(root),
            &EventData::AgentRegistered(AgentRegistered {
                display_name: short("alice"),
                primary_role: Role::Implementor,
                purpose: text("x"),
                product_base: None,
                product_branch: None,
                provider: None,
                model: None,
            }),
            [],
        );
        let bob_env = Envelope::new(
            &a("bob"),
            0,
            no_frontier(root),
            &EventData::AgentRegistered(AgentRegistered {
                display_name: short("bob"),
                primary_role: Role::Reviewer,
                purpose: text("x"),
                product_base: None,
                product_branch: None,
                provider: None,
                model: None,
            }),
            [],
        );
        crate::apply::reduce_onto(state, &[alice_env, bob_env]).unwrap()
    }

    fn review_request(authors: &[Agent], reviewer: &Agent, scope: &[&str]) -> ReviewNominated {
        ReviewNominated {
            authors: StringSet::from_iter(authors.iter().cloned()),
            product_branch: Branch::parse("refs/heads/agent/alice/feature".into()).unwrap(),
            reviewer: reviewer.clone(),
            required_checks: vec![],
            review_scope: StringSet::from_iter(
                scope
                    .iter()
                    .map(|s| crate::scalars::PathClaim::parse(s.to_string()).unwrap()),
            ),
            summary: text("s"),
            target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        }
    }

    /// Inserts a review chain (nominated by `alice`, naming `bob` as
    /// reviewer) with zero authorizations/receipts -- the starting point
    /// every test below either leaves alone (`flags_no_matching_
    /// authorization`) or adds an authorization/receipt to directly.
    fn insert_chain(state: &mut BusState) -> EventId {
        let nomination = EventId::new(&a("alice"), 1);
        let chain = ReviewChain {
            root: nomination.clone(),
            nomination_events: vec![nomination.clone()],
            current_nomination: nomination.clone(),
            current_request: review_request(&[a("alice")], &a("bob"), &["x.txt"]),
            nomination_reviewer: BTreeMap::from([(nomination.clone(), a("bob"))]),
            accepted_nominations: BTreeSet::from([nomination.clone()]),
            decline_or_withdraw_or_reassign_status: ItemStatus::Open,
            findings: BTreeMap::new(),
            authorizations: vec![],
            merged: vec![],
            reconciled: vec![],
        };
        state.reviews.insert(nomination.clone(), chain);
        state
            .review_chain_by_nomination
            .insert(nomination.clone(), nomination.clone());
        nomination
    }

    /// Appends a `review.merge_authorized` event (published by `bob`) to
    /// `nomination`'s chain naming exactly `(candidate, previous_main,
    /// reviewed_commit)`, and returns its id.
    fn insert_authorization(
        state: &mut BusState,
        nomination: &EventId,
        seq: u64,
        previous_main: &str,
        reviewed_commit: &str,
        candidate: &str,
    ) -> EventId {
        let root = state.review_chain_by_nomination[nomination].clone();
        let data = ReviewMergeAuthorized {
            nomination: nomination.clone(),
            product_branch: Branch::parse("refs/heads/agent/alice/feature".into()).unwrap(),
            previous_main: oid(previous_main),
            reviewed_commit: oid(reviewed_commit),
            candidate: oid(candidate),
            merge_engine_epoch: EventId::new(&a("bob"), 0),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter([crate::scalars::PathClaim::parse(
                "x.txt".into(),
            )
            .unwrap()]),
            limitations: vec![],
            summary: text("looks good"),
        };
        let env = Envelope::new(
            &a("bob"),
            seq,
            no_frontier(previous_main),
            &EventData::ReviewMergeAuthorized(data),
            [],
        );
        let id = env.id.clone();
        state.events.insert(id.clone(), env);
        state
            .reviews
            .get_mut(&root)
            .unwrap()
            .authorizations
            .push(id.clone());
        id
    }

    /// Appends a `review.merged` receipt (published by `bob`) naming
    /// `main_commit`, to the same chain `authorization` belongs to.
    fn insert_merged_receipt(
        state: &mut BusState,
        nomination: &EventId,
        seq: u64,
        authorization: &EventId,
        previous_main: &str,
        reviewed_commit: &str,
        main_commit: &str,
    ) -> EventId {
        let root = state.review_chain_by_nomination[nomination].clone();
        let data = ReviewMerged {
            authorization: authorization.clone(),
            previous_main: oid(previous_main),
            main_commit: oid(main_commit),
            product_branch: Branch::parse("refs/heads/agent/alice/feature".into()).unwrap(),
            reviewed_commit: oid(reviewed_commit),
            summary: text("merged"),
        };
        let env = Envelope::new(
            &a("bob"),
            seq,
            no_frontier(previous_main),
            &EventData::ReviewMerged(data),
            [],
        );
        let id = env.id.clone();
        state.events.insert(id.clone(), env);
        state
            .reviews
            .get_mut(&root)
            .unwrap()
            .merged
            .push(id.clone());
        id
    }

    /// As `insert_merged_receipt`, but the `review.merge_reconciled`
    /// recovery shape instead (AGENT_REVIEW.md section 11) -- published by
    /// `coord1` rather than the reviewer, mirroring that command's real
    /// coordinator-only authority.
    fn insert_reconciled_receipt(
        state: &mut BusState,
        nomination: &EventId,
        seq: u64,
        authorization: &EventId,
        previous_main: &str,
        reviewed_commit: &str,
        main_commit: &str,
    ) -> EventId {
        let root = state.review_chain_by_nomination[nomination].clone();
        let data = ReviewMergeReconciled {
            authorization: authorization.clone(),
            previous_main: oid(previous_main),
            main_commit: oid(main_commit),
            product_branch: Branch::parse("refs/heads/agent/alice/feature".into()).unwrap(),
            reviewed_commit: oid(reviewed_commit),
            reason: text("manual merge outside the bus"),
            user_authority: text("repo owner"),
        };
        let env = Envelope::new(
            &a("coord1"),
            seq,
            no_frontier(previous_main),
            &EventData::ReviewMergeReconciled(data),
            [],
        );
        let id = env.id.clone();
        state.events.insert(id.clone(), env);
        state
            .reviews
            .get_mut(&root)
            .unwrap()
            .reconciled
            .push(id.clone());
        id
    }

    fn problems(findings: &[Value]) -> Vec<String> {
        findings
            .iter()
            .map(|v| v["problem"].as_str().unwrap().to_string())
            .collect()
    }

    #[test]
    fn flags_non_merge_commit() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let stray = author_commit(dir.path(), &root, "stray.txt", Some("alice"));
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&stray)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("not a two-parent merge")),
            "{problems:?}"
        );
    }

    #[test]
    fn flags_missing_reviewer_trailer() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let merge = merge_commit(dir.path(), &root, &second, "merge without trailer");
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("missing or duplicate Agent-Bus-Reviewer trailer")),
            "{problems:?}"
        );
    }

    #[test]
    fn flags_duplicate_reviewer_trailer() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let merge = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob\nAgent-Bus-Reviewer: bob",
        );
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("missing or duplicate Agent-Bus-Reviewer trailer")),
            "{problems:?}"
        );
    }

    #[test]
    fn flags_non_reviewer_identity() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        // alice is a registered implementor, not a reviewer.
        let merge = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: alice",
        );
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems.iter().any(|p| p.contains("non-reviewer identity")),
            "{problems:?}"
        );
    }

    #[test]
    fn flags_a_reviewer_trailer_naming_an_unregistered_agent() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let merge = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: ghost",
        );
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems.iter().any(|p| p.contains("non-reviewer identity")),
            "an unregistered trailer name has no agents entry at all, so it must fall into the \
             same non-reviewer-identity bucket rather than panicking: {problems:?}"
        );
    }

    #[test]
    fn flags_missing_author_trailer() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "untrailered.txt", None);
        let merge = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("author trailer check failed")),
            "{problems:?}"
        );
    }

    #[test]
    fn flags_reviewer_authored_introduced_commit() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        // The introduced commit is trailered to bob, who is also the named
        // Agent-Bus-Reviewer on the merge itself.
        let second = author_commit(dir.path(), &root, "x.txt", Some("bob"));
        let merge = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("reviewer authored an introduced commit")),
            "{problems:?}"
        );
    }

    #[test]
    fn flags_no_matching_authorization() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        // Structurally plausible (right trailer, right roles, right
        // authorship) but no review.merge_authorized event names it.
        let merge = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );
        let mut state = base_state(&root);
        insert_chain(&mut state);
        let findings = audit_main_findings(dir.path(), &state, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("no review.merge_authorized matches")),
            "{problems:?}"
        );
    }

    /// AGENT_REVIEW.md section 9's correlation requires the *exact*
    /// candidate/previous_main/reviewed_commit of a real `review.merge_
    /// authorized` event, not merely "some authorization exists for a
    /// nomination with the same authors/reviewer". Build a genuinely
    /// authorized nomination (real candidate `authorized_candidate`), then
    /// present a *different* hand-built merge commit on the same
    /// previous_main/reviewed_commit pair, with the same authors and the
    /// same reviewer trailer -- everything a name-only correlation would
    /// accept -- but not the commit the authorization actually names. If
    /// `audit_main_findings` ever weakened its match to authors+reviewer
    /// only, this near-miss would wrongly correlate and the test would fail
    /// to see any finding.
    #[test]
    fn flags_authorized_nomination_but_wrong_exact_commit() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let authorized_candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "the real candidate\n\nAgent-Bus-Reviewer: bob",
        );
        let near_miss = merge_commit(
            dir.path(),
            &root,
            &second,
            "a different merge message\n\nAgent-Bus-Reviewer: bob",
        );
        assert_ne!(near_miss, authorized_candidate);

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        insert_authorization(
            &mut state,
            &nomination,
            1,
            &root,
            &second,
            &authorized_candidate,
        );

        let findings = audit_main_findings(dir.path(), &state, Some(&near_miss)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems.iter().any(|p| p.contains(
                "no review.merge_authorized matches this exact candidate/previous_main/reviewed_commit"
            )),
            "{problems:?}"
        );
    }

    #[test]
    fn flags_missing_receipt() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        // Authorized for real, but neither `review.merged` nor `review.
        // merge_reconciled` was ever published -- `main` advanced out of
        // band instead, the way a hand-pushed merge would.
        insert_authorization(&mut state, &nomination, 1, &root, &second, &candidate);

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("missing review.merged/review.merge_reconciled receipt")),
            "{problems:?}"
        );
    }

    #[test]
    fn clean_when_fully_correlated_via_merged_receipt() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        let auth_id = insert_authorization(&mut state, &nomination, 1, &root, &second, &candidate);
        insert_merged_receipt(
            &mut state,
            &nomination,
            2,
            &auth_id,
            &root,
            &second,
            &candidate,
        );

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate)).unwrap();
        assert!(findings.is_empty(), "{findings:?}");
    }

    /// The section 11 recovery path -- a `review.merge_reconciled` receipt
    /// must satisfy the correlation exactly as well as an ordinary `review.
    /// merged` one, since it is the documented substitute for exactly the
    /// case ("the reviewer merges but omits `review.merged`") this whole
    /// command exists to catch and does not itself resolve.
    #[test]
    fn clean_when_fully_correlated_via_reconciled_receipt() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        let auth_id = insert_authorization(&mut state, &nomination, 1, &root, &second, &candidate);
        insert_reconciled_receipt(
            &mut state,
            &nomination,
            2,
            &auth_id,
            &root,
            &second,
            &candidate,
        );

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate)).unwrap();
        assert!(findings.is_empty(), "{findings:?}");
    }

    /// A receipt naming a *different* `main_commit` than the one actually
    /// under audit must not satisfy this commit's own correlation -- proves
    /// `has_receipt`'s equality check is load-bearing, not merely "some
    /// receipt exists somewhere on the chain".
    #[test]
    fn a_receipt_for_a_different_commit_does_not_clear_this_ones_missing_receipt_finding() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );
        let other_candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "a different candidate\n\nAgent-Bus-Reviewer: bob",
        );
        assert_ne!(candidate, other_candidate);

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        let auth_id = insert_authorization(&mut state, &nomination, 1, &root, &second, &candidate);
        // Receipt names `other_candidate`, not the real `candidate` under audit.
        insert_merged_receipt(
            &mut state,
            &nomination,
            2,
            &auth_id,
            &root,
            &second,
            &other_candidate,
        );

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("missing review.merged/review.merge_reconciled receipt")),
            "{problems:?}"
        );
    }

    /// `to` defaults to `refs/heads/main` when not given -- the real CLI
    /// default (`cli::audit_main` passes `args.to.as_deref()` straight
    /// through). Confirmed by actually moving `refs/heads/main` and calling
    /// with `None`, not merely reading the constant.
    #[test]
    fn defaults_to_refs_heads_main_when_to_is_not_given() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let stray = author_commit(dir.path(), &root, "stray.txt", Some("alice"));
        git(dir.path(), &["update-ref", "refs/heads/main", &stray]);

        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, None).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("not a two-parent merge")),
            "{problems:?}"
        );
    }

    #[test]
    fn clean_when_no_commits_since_product_review_from() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let state = base_state(&root);
        let findings = audit_main_findings(dir.path(), &state, Some(&root)).unwrap();
        assert!(findings.is_empty(), "{findings:?}");
    }

    #[test]
    fn walks_multiple_commits_and_reports_a_finding_per_bad_one() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let good = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge\n\nAgent-Bus-Reviewer: bob",
        );
        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        let auth_id = insert_authorization(&mut state, &nomination, 1, &root, &second, &good);
        insert_merged_receipt(&mut state, &nomination, 2, &auth_id, &root, &second, &good);

        // A second, unrelated bad commit stacked directly on top of `good`.
        let third = author_commit(dir.path(), &good, "y.txt", Some("alice"));
        let bad = merge_commit(dir.path(), &good, &third, "merge without trailer");

        let findings = audit_main_findings(dir.path(), &state, Some(&bad)).unwrap();
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert_eq!(findings[0]["commit"], bad);
    }
}
