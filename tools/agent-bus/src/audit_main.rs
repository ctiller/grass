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
    // Every commit this audit will vouch for, so the receipt check below can
    // ask the *converse* question afterwards.
    let mut audited: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    audited.insert(previous.clone());
    for commit in commits {
        audited.insert(commit.clone());
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

        // A finding, not a `?`. One unreadable commit message anywhere in
        // post-bootstrap `main` must not abandon the whole audit: this is the
        // *only* authoritative place a bypass can be caught (sections 9/11/12),
        // so aborting would hide every later commit rather than reporting one.
        // The sibling call at `commit_authors_only`'s site below already
        // handles its error this way; this one did not, which was an
        // asymmetry rather than a decision. Reachable in practice because
        // `commit_message` reads the recorded bytes where `git show
        // --format=%B` transcoded through the commit's `encoding` header, so a
        // legacy commit declaring a non-UTF-8 encoding now errors here.
        let trailers = match crate::gitrepo::commit_message_trailers(repo, &commit) {
            Ok(t) => t,
            Err(e) => {
                findings.push(serde_json::json!({
                    "commit": commit,
                    "problem": format!("commit message could not be read for trailers: {e}"),
                }));
                previous = commit;
                continue;
            }
        };
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

        let mut matching: Option<(
            &crate::state::ReviewChain,
            crate::events::ReviewMergeAuthorized,
        )> = None;
        'chains: for chain in state.reviews.values() {
            let authors_match = introduced_authors
                == chain
                    .current_request
                    .authors
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<Agent>>();
            if !authors_match {
                continue;
            }
            for a_id in &chain.authorizations {
                if a_id.agent() != reviewer {
                    continue;
                }
                let Some(EventData::ReviewMergeAuthorized(auth)) =
                    state.events.get(a_id).and_then(|e| e.typed_data().ok())
                else {
                    continue;
                };
                if auth.candidate.as_str() == commit
                    && auth.previous_main.as_str() == previous
                    && auth.reviewed_commit.as_str() == reviewed_commit
                {
                    matching = Some((chain, auth));
                    break 'chains;
                }
            }
        }
        match matching {
            None => {
                findings.push(serde_json::json!({
                    "commit": commit,
                    "problem": "no review.merge_authorized matches this exact candidate/previous_main/reviewed_commit",
                    "reviewer": reviewer_name,
                }));
            }
            Some((chain, auth)) => {
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
                // AGENT_REVIEW.md section 12 fixture 6: "a candidate that...
                // contains unreviewed side content" must be caught here --
                // the only pre-push check for this (`merge_ready::check_
                // merge_ready`'s own scope check) is optional and skippable,
                // so this post-hoc correlation is the sole *authoritative*
                // place this crate can ever catch it (round-6 adversarial
                // review, reproduced live: a candidate whose introduced
                // content touched a file outside `reviewed_scope` audited
                // clean when `merge-ready` was simply never run).
                // A finding, not a `?`, for the same reason the trailer
                // read above is: this out-of-scope check is the sole
                // authoritative catch for section 12's fixture 6, so aborting
                // here would report *no* findings at all for the whole
                // history -- including ones already collected -- and a
                // candidate could hide behind that.
                //
                // Reachable for the same reason too: `diff_name_status` now
                // rejects a path that is not valid UTF-8, where the subprocess
                // it replaced returned `core.quotePath`'s ASCII-quoted form
                // instead. One Latin-1-named file used to be a quoted path and
                // is now a hard error.
                let changed = match crate::gitrepo::diff_name_status(repo, &previous, &commit) {
                    Ok(c) => c,
                    Err(e) => {
                        findings.push(serde_json::json!({
                            "commit": commit,
                            "problem": format!("changed paths could not be read: {e}"),
                        }));
                        previous = commit;
                        continue;
                    }
                };
                let out_of_scope: Vec<&str> = changed
                    .iter()
                    .filter(|(_, path)| {
                        !auth
                            .reviewed_scope
                            .iter()
                            .any(|claim| crate::merge_ready::path_in_claim(path, claim))
                    })
                    .map(|(_, path)| path.as_str())
                    .collect();
                if !out_of_scope.is_empty() {
                    findings.push(serde_json::json!({
                        "commit": commit,
                        "problem": "candidate changes paths outside the authorized reviewed_scope",
                        "reviewer": reviewer_name,
                        "paths": out_of_scope,
                    }));
                }
            }
        }
        previous = commit;
    }

    findings.extend(receipts_without_a_matching_commit(state, &audited));
    Ok(findings)
}

/// AGENT_REVIEW.md section 12, fixture 10: "a merge receipt not matching
/// product Git history".
///
/// The walk above asks, for each commit actually on `main`, whether the bus
/// authorized it. That is only half of fixture 10. Nothing asked the converse
/// -- whether every *receipt* names a commit that is really there -- and the
/// asymmetry was backwards: `review.merge_reconciled`, the recovery receipt
/// published by a third-party coordinator, is verified against live remote
/// `main` at publication time, while `review.merged`, the primary receipt on
/// which a reviewer's release from this chain hangs, was checked only for
/// field equality against its own authorization.
///
/// So a reviewer whose push lost a race could publish `review.merged` anyway.
/// Both gates accept it, and the audit stayed silent because the commit it
/// names is not on `main` and therefore never walked. The bus would durably
/// record a merge that never happened.
fn receipts_without_a_matching_commit(
    state: &BusState,
    audited: &std::collections::BTreeSet<String>,
) -> Vec<Value> {
    let mut findings = Vec::new();
    for chain in state.reviews.values() {
        for receipt in chain.merged.iter().chain(chain.reconciled.iter()) {
            let Some(env) = state.events.get(receipt) else {
                continue;
            };
            let named = match env.typed_data() {
                Ok(EventData::ReviewMerged(m)) => m.main_commit.as_str().to_string(),
                Ok(EventData::ReviewMergeReconciled(m)) => m.main_commit.as_str().to_string(),
                _ => continue,
            };
            if !audited.contains(&named) {
                findings.push(serde_json::json!({
                    "commit": named,
                    "problem": "a merge receipt names a commit that is not on the audited main history",
                    "receipt": receipt.as_str(),
                }));
            }
        }
    }
    findings
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

    /// A commit whose message this crate cannot read must produce a finding,
    /// not abandon the audit.
    ///
    /// This is reachable rather than theoretical: the message is now read
    /// from the object database, where `git show -s --format=%B` used to
    /// transcode through the commit's `encoding` header. A legacy commit
    /// declaring a non-UTF-8 encoding therefore errors where it once
    /// succeeded -- and `audit_main` is the *only* authoritative place a
    /// bypass can be caught (sections 9/11/12), so aborting on one commit
    /// would hide every commit after it.
    #[test]
    fn reports_an_unreadable_commit_message_as_a_finding_rather_than_aborting() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let tree = git(dir.path(), &["rev-parse", &format!("{second}^{{tree}}")]);

        // Hand-build the commit object: git's porcelain will not write a
        // message it cannot encode, and that is exactly the shape under test.
        let mut body = Vec::new();
        body.extend_from_slice(format!("tree {tree}\n").as_bytes());
        body.extend_from_slice(format!("parent {root}\n").as_bytes());
        body.extend_from_slice(format!("parent {second}\n").as_bytes());
        body.extend_from_slice(b"author T <t@e> 1700000000 +0000\n");
        body.extend_from_slice(b"committer T <t@e> 1700000000 +0000\n");
        body.extend_from_slice(b"encoding ISO-8859-1\n\n");
        // 0xe9 is `e`-acute in Latin-1 and invalid on its own in UTF-8.
        body.extend_from_slice(b"sujet accentu\xe9\n\nAgent-Bus-Reviewer: bob\n");

        let raw = dir.path().join("raw-commit");
        std::fs::write(&raw, &body).unwrap();
        let candidate = git(
            dir.path(),
            &["hash-object", "-t", "commit", "-w", &raw.to_string_lossy()],
        );
        std::fs::remove_file(&raw).unwrap();

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        insert_authorization(&mut state, &nomination, 1, &root, &second, &candidate);

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate))
            .expect("one unreadable message must not abort the audit");
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("commit message could not be read for trailers")),
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

    /// AGENT_REVIEW.md section 12 fixture 6: "a candidate that... contains
    /// unreviewed side content" -- round-6 adversarial review, reproduced
    /// live: everything else about this candidate is genuinely, exactly
    /// correlated (right authors, right reviewer, right authorization,
    /// right receipt) except that the reviewed commit introduces
    /// `sneaky.txt`, entirely outside the authorization's declared
    /// `reviewed_scope` (`insert_authorization` always authorizes exactly
    /// `x.txt`). Before this fix `audit-main` reported this fully clean.
    #[test]
    fn flags_a_candidate_that_touches_a_path_outside_reviewed_scope() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "sneaky.txt", Some("alice"));
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
        let scope_finding = findings
            .iter()
            .find(|f| {
                f["problem"]
                    .as_str()
                    .is_some_and(|p| p.contains("outside the authorized reviewed_scope"))
            })
            .unwrap_or_else(|| panic!("no scope finding among {findings:?}"));
        assert_eq!(
            scope_finding["paths"],
            serde_json::json!(["sneaky.txt"]),
            "{findings:?}"
        );
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

    /// AGENT_REVIEW.md sections 9/11: the authorization that clears a merge
    /// must be published by *that merge's own* reviewer, named in its
    /// `Agent-Bus-Reviewer` trailer. Deleting the `a_id.agent() != reviewer`
    /// guard let any reviewer's authorization clear any merge, and no test
    /// noticed, because every existing fixture used `bob` for both.
    #[test]
    fn an_authorization_published_by_a_different_reviewer_does_not_clear_a_merge() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        // The merge names `carol` as its reviewer ...
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge

Agent-Bus-Reviewer: carol",
        );

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        // ... but the only authorization on record was published by `bob`,
        // and otherwise matches this candidate exactly.
        insert_authorization(&mut state, &nomination, 1, &root, &second, &candidate);

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("no review.merge_authorized matches")),
            "an authorization by another reviewer must not clear this merge: {problems:?}"
        );
    }

    /// The chain is matched by the exact author set of the introduced
    /// commits (sections 3/7). A chain whose nomination names different
    /// authors is a different piece of work and must not supply the
    /// authorization for this one.
    #[test]
    fn a_chain_whose_authors_differ_does_not_supply_the_authorization() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        // Introduced content authored by `dave`; the only chain on record
        // names `alice`.
        let second = author_commit(dir.path(), &root, "x.txt", Some("dave"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge

Agent-Bus-Reviewer: bob",
        );

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        insert_authorization(&mut state, &nomination, 1, &root, &second, &candidate);

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("no review.merge_authorized matches")),
            "a chain with a different author set must not match: {problems:?}"
        );
    }

    /// All three of `candidate`, `previous_main` and `reviewed_commit` must
    /// agree. Matching on the candidate alone would accept an authorization
    /// issued against a different base -- the reviewer approved merging that
    /// work onto *some other* main, which is not what happened here.
    #[test]
    fn an_authorization_naming_a_different_previous_main_does_not_match() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge

Agent-Bus-Reviewer: bob",
        );
        let elsewhere = author_commit(dir.path(), &root, "unrelated.txt", Some("alice"));
        assert_ne!(elsewhere, root);

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        // Right candidate, right reviewed_commit, wrong previous_main.
        insert_authorization(&mut state, &nomination, 1, &elsewhere, &second, &candidate);

        let findings = audit_main_findings(dir.path(), &state, Some(&candidate)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("no review.merge_authorized matches")),
            "a near-miss authorization must not clear the merge: {problems:?}"
        );
    }

    /// The audited history must be a first-parent chain: each merge's *first*
    /// parent is the commit audited before it. A two-parent merge whose
    /// parents are the other way round would otherwise pass the arity check
    /// and then be read with `parents[1]` as the reviewed commit -- naming
    /// the previous main as the reviewed work.
    #[test]
    fn a_merge_whose_first_parent_is_not_the_prior_main_commit_is_flagged() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        // The audit starts from `start`; `sidestep` is a sibling of it, so
        // the merge below rejoins the history *beside* the audited base
        // rather than on top of it. Simply reversing a merge's parents does
        // not express this: the walk follows first parents, so `previous`
        // advances to whatever the first parent was and the check passes.
        // The violation only exists at the first audited commit, where
        // `previous` is `product_review_from` itself.
        let start = author_commit(dir.path(), &root, "start.txt", Some("alice"));
        let sidestep = author_commit(dir.path(), &root, "side.txt", Some("alice"));
        let backwards = merge_commit(
            dir.path(),
            &root,
            &sidestep,
            "merge

Agent-Bus-Reviewer: bob",
        );

        let state = base_state(&start);
        let findings = audit_main_findings(dir.path(), &state, Some(&backwards)).unwrap();

        // Asserted against *this* commit, not merely against the message.
        // An earlier version of this test searched only for the message, and
        // was vacuous: its fixture's walk also contained a non-merge commit
        // reporting the identical problem, so it passed with the
        // first-parent clause deleted. This fixture's walk is the single
        // commit below, and the assertion names it.
        let flagged_backwards = findings.iter().any(|f| {
            f["commit"].as_str() == Some(backwards.as_str())
                && f["problem"]
                    .as_str()
                    .unwrap_or_default()
                    .contains("not a two-parent merge whose first parent is the prior audited main")
        });
        assert!(
            flagged_backwards,
            "the reversed-parent merge itself must be flagged: {findings:?}"
        );
    }

    /// AGENT_REVIEW.md section 12 fixture 10, the direction that was missing:
    /// a receipt naming a commit that never reached `main`.
    ///
    /// The realistic path is a lost push race -- the reviewer's
    /// `git push <candidate>:refs/heads/main` is rejected because `main`
    /// advanced, and they publish `review.merged` regardless. Both the
    /// coordinator gate and reduction accept it (they compare it against its
    /// own authorization, not against git), and the walk never sees it
    /// because the commit is not on `main`.
    /// A receipt naming a *different* `main_commit` than the one actually
    /// under audit must not satisfy this commit's own correlation -- proves
    /// `has_receipt`'s equality check is load-bearing, not merely "some
    /// receipt exists somewhere on the chain".
    #[test]
    fn flags_a_merge_receipt_naming_a_commit_that_is_not_on_main() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge

Agent-Bus-Reviewer: bob",
        );
        // A candidate that was built but never landed: `main` stays at root.
        let never_pushed = merge_commit(
            dir.path(),
            &root,
            &second,
            "a candidate that lost the push race

Agent-Bus-Reviewer: bob",
        );
        assert_ne!(candidate, never_pushed);

        let mut state = base_state(&root);
        let nomination = insert_chain(&mut state);
        let auth_id =
            insert_authorization(&mut state, &nomination, 1, &root, &second, &never_pushed);
        insert_merged_receipt(
            &mut state,
            &nomination,
            2,
            &auth_id,
            &root,
            &second,
            &never_pushed,
        );

        // Audit `main`, which never moved.
        let findings = audit_main_findings(dir.path(), &state, Some(&root)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems
                .iter()
                .any(|p| p.contains("names a commit that is not on the audited main history")),
            "a receipt for a commit that never landed must be flagged: {problems:?}"
        );
    }

    /// The companion: an honest receipt for a commit that *is* on `main` must
    /// not be flagged, or the check above would fire on every healthy bus.
    #[test]
    fn does_not_flag_a_merge_receipt_for_a_commit_that_is_on_main() {
        let dir = init_repo();
        let root = git(dir.path(), &["rev-parse", "main"]);
        let second = author_commit(dir.path(), &root, "x.txt", Some("alice"));
        let candidate = merge_commit(
            dir.path(),
            &root,
            &second,
            "merge

Agent-Bus-Reviewer: bob",
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
        let problems = problems(&findings);
        assert!(
            !problems
                .iter()
                .any(|p| p.contains("names a commit that is not on the audited main history")),
            "an honest receipt must not be flagged: {problems:?}"
        );
    }

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
