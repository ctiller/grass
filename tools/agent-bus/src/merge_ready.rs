//! AGENT_REVIEW.md section 8, the pre-merge gate: the reviewer runs this
//! immediately after publishing `review.merge_authorized` and immediately
//! before pushing the resulting candidate to `main`.
//!
//! Distinct from, and later than, both `apply::apply_review_merge_authorized`
//! (the event's own internal bus-state consistency, checked once at
//! reduction time) and `coordinator::verify_review_merge_authorized`
//! (git-linked checks against the *submitted payload*, checked once at
//! publication time): real time passes between publishing the authorization
//! and actually pushing the candidate, during which `main` may have
//! advanced, or the candidate object itself could have been hand-tampered
//! with -- neither of those earlier gates can catch that, since both run
//! once, at or before publication. This is the one check that reads live
//! Git/bus state as of the moment it is actually run.
//!
//! Ported closely from the shipped version-one helper's `review_cmds::
//! merge_ready` (see its own ~dozen `merge_ready_rejects_*` tests) onto v2's
//! `BusState`/`sync::Snapshot` primitives. `cli::merge_ready` is the thin CLI
//! wrapper (arg parsing, snapshot load, JSON output) around [`check_merge_
//! ready`] below -- mirroring how `cli::prepare_merge` wraps `merge_
//! candidate::verify_authorship`/`reconstruct_candidate`.

use crate::error::{invalid, AbResult};
use crate::events::{EventData, ReviewMergeAuthorized};
use crate::scalars::{Agent, EventId, ObjectId, PathClaim};
use crate::state::{BusState, FindingDisposition};
use std::path::Path;

/// AGENT_REVIEW.md section 8: `path` (one line of a `git diff --name-status`
/// listing) falls within `claim`'s scope -- either an exact match, or `claim`
/// names a `/**`-suffixed directory prefix `path` falls under. Deliberately
/// mirrors `scalars::PathClaim::overlaps`'s own prefix logic rather than
/// reusing it directly: `overlaps` compares two *claims* (each side may carry
/// its own `/**` suffix), while a changed path from `git diff` is a plain
/// repo-relative file path that is never itself glob-suffixed -- ported
/// as-is from the shipped version-one helper's `review_cmds::path_in_claim`.
pub(crate) fn path_in_claim(path: &str, claim: &PathClaim) -> bool {
    match claim.as_str().strip_suffix("/**") {
        Some(prefix) => path == prefix || path.starts_with(&format!("{prefix}/")),
        None => path == claim.as_str(),
    }
}

/// The full gate (AGENT_REVIEW.md section 8). `state` is an ordinary bus
/// snapshot -- `cli::merge_ready` passes `sync::synced_snapshot`'s, a fresh
/// remote probe, *not* a cached one: `reviewed_scope` and the nomination
/// chain's own shape are fixed at authorization-publication time, but a
/// finding can be reopened, or a new blocking issue opened, by a completely
/// different agent in the real time that elapses between authorization and
/// this check -- exactly the kind of concurrent change this gate exists to
/// catch (round-6 adversarial review: a cached snapshot let an unsynced
/// checkout report `ready: true` past a blocking issue another host had
/// already published). The live-Git half below fetches `refs/heads/main`
/// from `remote` for the identical reason, rather than trusting whatever
/// this checkout's own local `main` happens to be -- `main` moving is
/// exactly the kind of concurrent change this gate exists to catch, and a
/// checkout that hasn't independently fetched `main` itself would otherwise
/// silently pass a stale check (round-7 adversarial review: `check_merge_
/// ready` claimed this guarantee here without actually fetching -- the same
/// checkout-dependence bug already found and fixed twice elsewhere in this
/// module's siblings, `coordinator::verify_review_merge_authorized`/`verify_
/// review_merge_reconciled`). `auth.candidate` itself is still read as
/// whatever this checkout already has locally, like `prepare-merge` -- the
/// reviewer is expected to have already fetched or constructed it themselves
/// (per AGENT_REVIEW.md section 7 step 1). Returns the exact candidate
/// object id to push on success.
pub(crate) fn check_merge_ready(
    repo: &Path,
    remote: &str,
    state: &BusState,
    reviewer: &Agent,
    authorization: &EventId,
) -> AbResult<ObjectId> {
    let auth_env = state
        .events
        .get(authorization)
        .ok_or_else(|| invalid(format!("unknown authorization {authorization}")))?;
    let auth: ReviewMergeAuthorized = match auth_env.typed_data()? {
        EventData::ReviewMergeAuthorized(d) => d,
        _ => {
            return Err(invalid(format!(
                "{authorization} is not a review.merge_authorized event"
            )))
        }
    };
    if auth_env.agent != *reviewer {
        return Err(invalid(format!(
            "authorization {authorization} was published by {}, not the given reviewer {reviewer}",
            auth_env.agent
        )));
    }
    let chain = state
        .review_chain(&auth.nomination)
        .ok_or_else(|| invalid("unknown nomination for this authorization"))?;
    if chain.current_request.reviewer != *reviewer || !chain.accepted() {
        return Err(invalid(
            "reviewer is not the accepted eligible reviewer for this nomination",
        ));
    }
    for f in chain.findings.values() {
        if f.disposition == FindingDisposition::Open {
            return Err(invalid(format!(
                "finding {} has no terminal disposition",
                f.finding_id
            )));
        }
    }
    // Shared with `apply::apply_review_merge_authorized`'s own identical
    // check (factored out specifically so this gate and that one can never
    // drift) -- see `apply::blocking_issue_for_chain`'s doc comment.
    if let Some(blocking) = crate::apply::blocking_issue_for_chain(state, chain) {
        return Err(invalid(format!(
            "issue {blocking} explicitly blocks this nomination chain"
        )));
    }
    // In ordinary reduction this can never actually differ: `apply_review_
    // merge_authorized` already required `d.reviewed_scope == chain.current_
    // request.review_scope` at publication time, and `apply_review_
    // reassigned` requires every reassignment's request to be identical to
    // `chain.current_request` except the reviewer field, so `review_scope`
    // itself can never move underneath an already-published authorization.
    // Kept anyway as a genuine defense-in-depth check (mirrors v1, which
    // carries the identical check for the identical reason) against any
    // future relaxation of either invariant, or a chain reached by a path
    // this crate's own reduction rules do not yet anticipate.
    if auth.reviewed_scope != chain.current_request.review_scope {
        return Err(invalid(
            "authorization reviewed_scope does not exactly equal the nomination's review_scope",
        ));
    }

    // Everything above is a pure bus-state check, answerable from `state`
    // alone. Everything below is genuinely time-sensitive: it re-reads live
    // Git state that could only have changed in the real time that elapsed
    // since `review.merge_authorized` was published -- the whole reason this
    // gate exists as a distinct, later check from `coordinator::verify_
    // review_merge_authorized` (which validates the same payload once, at
    // publication time).
    // `refs/heads/main` is a product ref entirely outside `sync::synced_
    // snapshot`'s fetch (registry/agent-event refs only) -- reading it
    // locally without first fetching would make this check checkout
    // -dependent, exactly the bug round 5/6 already found and fixed for
    // `verify_review_merge_authorized`/`verify_review_merge_reconciled`
    // (round-7 review: this gate's own doc above claims "repo is read
    // directly and uncached for the live-Git half... like main moving",
    // which is only true once this fetch actually happens). Fetched into a
    // scratch ref rather than the local `refs/heads/main` itself, so this
    // never touches whatever the caller's own working tree has checked out.
    const MAIN_PROBE_REF: &str = "refs/agent-bus/merge-ready-main-probe";
    let fetch = crate::gitrepo::fetch_refspecs(
        repo,
        remote,
        &[format!("refs/heads/main:{MAIN_PROBE_REF}")],
    )?;
    if !fetch.success {
        return Err(invalid(format!(
            "could not fetch refs/heads/main from {remote} to verify this merge is still ready: {}",
            fetch.stderr
        )));
    }
    let current_main = crate::gitrepo::rev_parse(repo, MAIN_PROBE_REF)?;
    if current_main != auth.previous_main.as_str() {
        return Err(invalid(format!(
            "current main {current_main} has advanced past authorized previous_main {}",
            auth.previous_main
        )));
    }
    let parents = crate::gitrepo::parents_of(repo, auth.candidate.as_str())?;
    if parents
        != vec![
            auth.previous_main.as_str().to_string(),
            auth.reviewed_commit.as_str().to_string(),
        ]
    {
        return Err(invalid(
            "candidate parents do not match previous_main/reviewed_commit in order",
        ));
    }
    let trailers = crate::gitrepo::commit_message_trailers(repo, auth.candidate.as_str())?;
    let reviewer_trailers: Vec<&(String, String)> = trailers
        .iter()
        .filter(|(k, _)| k == "Agent-Bus-Reviewer")
        .collect();
    if reviewer_trailers.len() != 1 || reviewer_trailers[0].1 != reviewer.as_str() {
        return Err(invalid(
            "candidate must have exactly one matching Agent-Bus-Reviewer trailer",
        ));
    }
    let changed = crate::gitrepo::diff_name_status(repo, &current_main, auth.candidate.as_str())?;
    for (_, path) in &changed {
        if !auth.reviewed_scope.iter().any(|p| path_in_claim(path, p)) {
            return Err(invalid(format!(
                "changed path {path} is outside reviewed_scope"
            )));
        }
    }
    // `common::CheckOutcome` currently has `Passed` as its sole variant (a
    // failed check is reported through `progress.reported`, never recorded
    // in `checks` here -- see the enum's own doc comment), so this loop
    // cannot presently be falsified by any value the type system allows to
    // be constructed. Kept for structural parity with v1 (which has a
    // richer `CheckOutcome`) and so this gate does not silently stop
    // checking the moment a `Failed`-or-similar variant is ever added.
    for c in &auth.checks {
        if c.result != crate::common::CheckOutcome::Passed {
            return Err(invalid("a required check result is not passed"));
        }
    }

    Ok(auth.candidate)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{CheckOutcome, CheckResult};
    use crate::envelope::Envelope;
    use crate::events::{AgentRegistered, IssueKind, IssueOpened, ReviewNominated, Role};
    use crate::frontier::ObservedFrontier;
    use crate::scalars::{Branch, ObjectId, Short, StringSet, Text};
    use crate::state::{FindingState, IssueState, ItemStatus, ReviewChain};
    use std::collections::{BTreeMap, BTreeSet};
    use std::path::{Path, PathBuf};

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn short(s: &str) -> Short {
        Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> Text {
        Text::parse(s.to_string()).unwrap()
    }

    fn path_claim(s: &str) -> PathClaim {
        PathClaim::parse(s.to_string()).unwrap()
    }

    fn hash(n: u64) -> ObjectId {
        ObjectId::parse(format!("{n:040x}")).unwrap()
    }

    fn config() -> crate::bootstrap::BusConfig {
        crate::bootstrap::BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: hash(1),
            merge_engine: crate::bootstrap::SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
        }
    }

    fn no_frontier() -> ObservedFrontier {
        ObservedFrontier::sparse(hash(1), [])
    }

    fn review_request(authors: &[Agent], reviewer: &Agent, scope: &[&str]) -> ReviewNominated {
        ReviewNominated {
            authors: StringSet::from_iter(authors.iter().cloned()),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            reviewer: reviewer.clone(),
            required_checks: vec![],
            review_scope: StringSet::from_iter(scope.iter().map(|s| path_claim(s))),
            summary: text("s"),
            target_branch: Branch::parse("refs/heads/main".into()).unwrap(),
            evidence: StringSet::default(),
        }
    }

    /// Hand-builds a minimal `BusState` containing exactly one review chain
    /// (nominated by `author`, naming `reviewer`) and one `review.merge_
    /// authorized` event published by `auth_agent` -- deliberately *not*
    /// built by running the real event-reduction path
    /// (`apply::apply_event`), since several of the branches below (an
    /// unaccepted/ineligible reviewer, an unresolved finding, a blocking
    /// issue, a `reviewed_scope` mismatch) need to construct states `check_
    /// merge_ready` must reject that ordinary reduction would refuse to
    /// produce in the first place -- exactly the "what if this gate is ever
    /// reached with an invariant violated some other way" defense-in-depth
    /// case each corresponding production check exists for. `accepted`
    /// controls whether `reviewer` is recorded as having accepted the
    /// nomination; `auth_reviewed_scope` is independent of `request_scope`
    /// so a mismatch can be constructed directly.
    #[allow(clippy::too_many_arguments)]
    fn fixture(
        author: &Agent,
        reviewer: &Agent,
        auth_agent: &Agent,
        accepted: bool,
        request_scope: &[&str],
        auth_reviewed_scope: &[&str],
        findings: Vec<FindingState>,
        issues: Vec<IssueState>,
    ) -> (BusState, EventId, EventId) {
        let mut state = BusState::new(config());
        let nomination = EventId::new(author, 0);

        let mut nomination_reviewer = BTreeMap::new();
        nomination_reviewer.insert(nomination.clone(), reviewer.clone());
        let mut accepted_nominations = BTreeSet::new();
        if accepted {
            accepted_nominations.insert(nomination.clone());
        }
        let findings_map: BTreeMap<(EventId, String), FindingState> = findings
            .into_iter()
            .map(|f| {
                (
                    (f.changes_event.clone(), f.finding_id.as_str().to_string()),
                    f,
                )
            })
            .collect();
        let chain = ReviewChain {
            root: nomination.clone(),
            nomination_events: vec![nomination.clone()],
            current_nomination: nomination.clone(),
            current_request: review_request(std::slice::from_ref(author), reviewer, request_scope),
            nomination_reviewer,
            accepted_nominations,
            decline_or_withdraw_or_reassign_status: ItemStatus::Open,
            findings: findings_map,
            authorizations: vec![],
            merged: vec![],
            reconciled: vec![],
        };
        state.reviews.insert(nomination.clone(), chain);
        state
            .review_chain_by_nomination
            .insert(nomination.clone(), nomination.clone());

        for issue in issues {
            state.issues.insert(issue.id.clone(), issue);
        }

        let auth_data = ReviewMergeAuthorized {
            nomination: nomination.clone(),
            product_branch: Branch::parse("refs/heads/agent/alice/x".into()).unwrap(),
            previous_main: hash(2),
            reviewed_commit: hash(3),
            candidate: hash(4),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![CheckResult {
                command: text("build"),
                result: CheckOutcome::Passed,
                evidence: None,
            }],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter(auth_reviewed_scope.iter().map(|s| path_claim(s))),
            limitations: vec![],
            summary: text("s"),
        };
        let auth_env = Envelope::new(
            auth_agent,
            0,
            no_frontier(),
            &EventData::ReviewMergeAuthorized(auth_data),
            [],
        );
        let auth_id = auth_env.id.clone();
        state.events.insert(auth_id.clone(), auth_env);

        (state, nomination, auth_id)
    }

    fn issue_blocking(id: &EventId, target: &Agent, blocks: &EventId) -> IssueState {
        IssueState {
            id: id.clone(),
            opener: target.clone(),
            data: IssueOpened {
                target: target.clone(),
                issue_kind: IssueKind::Bug,
                severity: crate::common::Priority::Normal,
                summary: text("blocking bug"),
                code_commit: None,
                locations: vec![],
                expected: None,
                observed_behavior: None,
                reproduction: vec![],
                blocks: StringSet::from_iter([blocks.clone()]),
                evidence: StringSet::default(),
            },
            current_target: target.clone(),
            current_assignment: id.clone(),
            assignment_target: BTreeMap::new(),
            acknowledged_assignments: BTreeSet::new(),
            status: ItemStatus::Open,
            resolution_summary: None,
            reassignment_chain: vec![],
        }
    }

    // ---------------------------------------------------------- bus-state-only

    #[test]
    fn rejects_unknown_authorization() {
        let (state, _nomination, _auth_id) = fixture(
            &a("zoe"),
            &a("aiden"),
            &a("aiden"),
            true,
            &["x"],
            &["x"],
            vec![],
            vec![],
        );
        let bogus = EventId::new(&a("aiden"), 99);
        let err = check_merge_ready(&PathBuf::from("."), "origin", &state, &a("aiden"), &bogus)
            .unwrap_err();
        assert!(err.to_string().contains("unknown authorization"), "{err}");
    }

    #[test]
    fn rejects_an_authorization_id_naming_a_different_kind_of_event() {
        let mut state = BusState::new(config());
        let agent = a("aiden");
        let data = EventData::AgentRegistered(AgentRegistered {
            display_name: short("aiden"),
            primary_role: Role::Reviewer,
            purpose: text("x"),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let env = Envelope::new(&agent, 0, no_frontier(), &data, []);
        let id = env.id.clone();
        state.events.insert(id.clone(), env);
        let err =
            check_merge_ready(&PathBuf::from("."), "origin", &state, &agent, &id).unwrap_err();
        assert!(
            err.to_string()
                .contains("is not a review.merge_authorized event"),
            "{err}"
        );
    }

    #[test]
    fn rejects_wrong_authorizer() {
        let (state, _nomination, auth_id) = fixture(
            &a("zoe"),
            &a("aiden"),
            &a("aiden"),
            true,
            &["x"],
            &["x"],
            vec![],
            vec![],
        );
        let err = check_merge_ready(&PathBuf::from("."), "origin", &state, &a("carol"), &auth_id)
            .unwrap_err();
        assert!(
            err.to_string()
                .contains("was published by aiden, not the given reviewer carol"),
            "{err}"
        );
    }

    #[test]
    fn rejects_a_reviewer_who_never_accepted() {
        let (state, _nomination, auth_id) = fixture(
            &a("zoe"),
            &a("aiden"),
            &a("aiden"),
            false, // never accepted
            &["x"],
            &["x"],
            vec![],
            vec![],
        );
        let err = check_merge_ready(&PathBuf::from("."), "origin", &state, &a("aiden"), &auth_id)
            .unwrap_err();
        assert!(
            err.to_string()
                .contains("not the accepted eligible reviewer"),
            "{err}"
        );
    }

    #[test]
    fn rejects_an_open_finding() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let nomination = EventId::new(&author, 0);
        let finding = FindingState {
            changes_event: EventId::new(&reviewer, 1),
            finding_id: short("f1"),
            priority: crate::common::Priority::Normal,
            locations: vec![],
            rationale: text("late finding"),
            closure_conditions: text("fix it"),
            disposition: FindingDisposition::Open,
        };
        let (state, _nomination, auth_id) = fixture(
            &author,
            &reviewer,
            &reviewer,
            true,
            &["x"],
            &["x"],
            vec![finding],
            vec![],
        );
        let _ = nomination;
        let err = check_merge_ready(&PathBuf::from("."), "origin", &state, &reviewer, &auth_id)
            .unwrap_err();
        assert!(
            err.to_string().contains("has no terminal disposition"),
            "{err}"
        );
    }

    #[test]
    fn rejects_a_blocking_issue() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let nomination = EventId::new(&author, 0);
        let issue_id = EventId::new(&author, 5);
        let issue = issue_blocking(&issue_id, &author, &nomination);
        let (state, _nomination, auth_id) = fixture(
            &author,
            &reviewer,
            &reviewer,
            true,
            &["x"],
            &["x"],
            vec![],
            vec![issue],
        );
        let err = check_merge_ready(&PathBuf::from("."), "origin", &state, &reviewer, &auth_id)
            .unwrap_err();
        assert!(
            err.to_string()
                .contains("explicitly blocks this nomination chain"),
            "{err}"
        );
    }

    /// A resolved (`Terminal`) issue whose `blocks` set still names the
    /// nomination must not block -- disposition is permanent, so only a
    /// genuinely unresolved issue counts (mirrors `apply::blocking_issue_
    /// for_chain`'s own doc comment). Reaching this branch instead of the
    /// blocking-issue rejection above proves the `Terminal` guard is
    /// actually load-bearing, not merely present.
    #[test]
    fn a_resolved_issue_does_not_block() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let nomination = EventId::new(&author, 0);
        let issue_id = EventId::new(&author, 5);
        let mut issue = issue_blocking(&issue_id, &author, &nomination);
        issue.status = ItemStatus::Terminal("resolved");
        let (state, _nomination, auth_id) = fixture(
            &author,
            &reviewer,
            &reviewer,
            true,
            &["x"],
            &["x"],
            vec![],
            vec![issue],
        );
        // Everything else about this fixture is deliberately valid at the
        // bus-state layer; the only way to reach the (repo-dependent) parent
        // check below with a bogus `Path` is for every state-only check,
        // including the resolved-issue non-block, to have passed first.
        let err = check_merge_ready(&PathBuf::from("."), "origin", &state, &reviewer, &auth_id)
            .unwrap_err();
        assert!(
            !err.to_string().contains("blocks this nomination chain"),
            "a Terminal issue must not block: {err}"
        );
    }

    /// `apply_review_merge_authorized` already requires `reviewed_scope ==
    /// review_scope` at publication time, and `apply_review_reassigned`
    /// requires every reassignment to copy `review_scope` unchanged -- so no
    /// sequence of real events can ever make this branch fire. Exercised
    /// here directly against a hand-built state (see `fixture`'s own doc
    /// comment) as a defense-in-depth check on the gate itself, not a
    /// reachable production scenario.
    #[test]
    fn rejects_a_reviewed_scope_mismatch() {
        let (state, _nomination, auth_id) = fixture(
            &a("zoe"),
            &a("aiden"),
            &a("aiden"),
            true,
            &["feature.txt"],
            &["other.txt"], // deliberately different from request_scope
            vec![],
            vec![],
        );
        let err = check_merge_ready(&PathBuf::from("."), "origin", &state, &a("aiden"), &auth_id)
            .unwrap_err();
        assert!(
            err.to_string()
                .contains("does not exactly equal the nomination's review_scope"),
            "{err}"
        );
    }

    // ------------------------------------------------------------- live-Git

    fn git(dir: &Path, args: &[&str]) {
        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?} failed in {}", dir.display());
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

    /// A real bare repository, standing in for a remote -- `check_merge_
    /// ready` fetches `refs/heads/main` from a real `remote` rather than
    /// trusting the caller's own local ref (round-7 review), so every
    /// live-Git test below needs one.
    fn init_bare_origin() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        git(dir.path(), &["init", "--quiet", "--bare", "-b", "main"]);
        dir
    }

    fn push_main(dir: &Path, remote: &str) {
        let push = crate::gitrepo::run(dir, &["push", remote, "refs/heads/main"]).unwrap();
        assert!(push.success, "{push:?}");
    }

    fn rev_parse(dir: &Path, rev: &str) -> String {
        crate::gitrepo::rev_parse(dir, rev).unwrap()
    }

    /// A real repo with `main` at one commit (already pushed to a real bare
    /// `origin`), a `feature` commit on top (carrying `Agent-Bus-Agent:
    /// <author>`) touching `feature.txt`, and the genuine
    /// merge-tree-write-tree candidate for `(main, feature, reviewer)` --
    /// everything `check_merge_ready`'s live-Git half needs. Returns `(dir,
    /// origin, remote, previous_main, feature_commit, candidate)`; `origin`
    /// must be kept alive by the caller for as long as `remote` is used.
    fn git_fixture(
        author: &Agent,
        reviewer: &Agent,
    ) -> (
        tempfile::TempDir,
        tempfile::TempDir,
        String,
        String,
        String,
        String,
    ) {
        let dir = init_repo();
        let path = dir.path();
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();
        push_main(path, &remote);
        let previous_main = rev_parse(path, "main");
        // Commit the feature detached from `main`, so `main` itself stays at
        // `previous_main` -- exactly like the reviewer's real workflow
        // (AGENT_REVIEW.md section 7): the product branch advances on its
        // own ref, `main` only moves once the reviewer's candidate is
        // actually pushed.
        git(path, &["checkout", "--quiet", "--detach", &previous_main]);
        std::fs::write(path.join("feature.txt"), "feature content\n").unwrap();
        git(path, &["add", "."]);
        git(
            path,
            &[
                "commit",
                "-q",
                "-m",
                &format!("add feature\n\nAgent-Bus-Agent: {author}"),
            ],
        );
        let feature_commit = rev_parse(path, "HEAD");
        let candidate = crate::merge_candidate::reconstruct_candidate(
            path,
            &previous_main,
            &feature_commit,
            reviewer,
        )
        .unwrap();
        git(path, &["checkout", "--quiet", "main"]);
        (
            dir,
            origin,
            remote,
            previous_main,
            feature_commit,
            candidate,
        )
    }

    /// Builds a state whose single review chain/authorization names exactly
    /// `previous_main`/`reviewed_commit`/`candidate`/`reviewed_scope` --
    /// shared by every git-linked test below so each one only has to say
    /// what's actually different about it (usually just `candidate`),
    /// rather than repeating this whole shape and risking one copy drifting
    /// from another.
    fn state_with_authorization(
        author: &Agent,
        reviewer: &Agent,
        previous_main: &str,
        reviewed_commit: &str,
        candidate: &str,
        reviewed_scope: &[&str],
    ) -> (BusState, EventId) {
        let mut state = BusState::new(config());
        let nomination = EventId::new(author, 0);
        let mut nomination_reviewer = BTreeMap::new();
        nomination_reviewer.insert(nomination.clone(), reviewer.clone());
        let mut accepted_nominations = BTreeSet::new();
        accepted_nominations.insert(nomination.clone());
        let chain = ReviewChain {
            root: nomination.clone(),
            nomination_events: vec![nomination.clone()],
            current_nomination: nomination.clone(),
            current_request: review_request(std::slice::from_ref(author), reviewer, reviewed_scope),
            nomination_reviewer,
            accepted_nominations,
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

        let auth_data = ReviewMergeAuthorized {
            nomination: nomination.clone(),
            product_branch: Branch::parse("refs/heads/agent/zoe/feature".into()).unwrap(),
            previous_main: ObjectId::parse(previous_main.to_string()).unwrap(),
            reviewed_commit: ObjectId::parse(reviewed_commit.to_string()).unwrap(),
            candidate: ObjectId::parse(candidate.to_string()).unwrap(),
            merge_engine_epoch: EventId::new(&a("coord1"), 0),
            checks: vec![CheckResult {
                command: text("build"),
                result: CheckOutcome::Passed,
                evidence: None,
            }],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter(reviewed_scope.iter().map(|s| path_claim(s))),
            limitations: vec![],
            summary: text("looks good"),
        };
        let auth_env = Envelope::new(
            reviewer,
            0,
            no_frontier(),
            &EventData::ReviewMergeAuthorized(auth_data),
            [],
        );
        let auth_id = auth_env.id.clone();
        state.events.insert(auth_id.clone(), auth_env);
        (state, auth_id)
    }

    /// A single hand-crafted `commit-tree` built on top of `feature_commit`'s
    /// tree, with whatever `parents`/`message` the caller names -- the
    /// common shape behind every "hand-pushed forged candidate" test below.
    fn commit_tree_with(
        dir: &Path,
        feature_commit: &str,
        parents: &[&str],
        message: &str,
    ) -> String {
        let tree =
            crate::gitrepo::run_ok(dir, &["rev-parse", &format!("{feature_commit}^{{tree}}")])
                .unwrap();
        let mut args = vec!["commit-tree", tree.trim()];
        for p in parents {
            args.push("-p");
            args.push(p);
        }
        args.push("-m");
        args.push(message);
        crate::gitrepo::run_ok(dir, &args)
            .unwrap()
            .trim()
            .to_string()
    }

    #[test]
    fn accepts_a_genuinely_valid_authorization_and_returns_the_candidate() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let (dir, _origin, remote, previous_main, feature_commit, candidate) =
            git_fixture(&author, &reviewer);
        let (state, auth_id) = state_with_authorization(
            &author,
            &reviewer,
            &previous_main,
            &feature_commit,
            &candidate,
            &["feature.txt"],
        );
        let got = check_merge_ready(dir.path(), &remote, &state, &reviewer, &auth_id).unwrap();
        assert_eq!(got.as_str(), candidate);
    }

    #[test]
    fn rejects_main_having_advanced_past_previous_main() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let (dir, _origin, remote, previous_main, feature_commit, candidate) =
            git_fixture(&author, &reviewer);
        let (state, auth_id) = state_with_authorization(
            &author,
            &reviewer,
            &previous_main,
            &feature_commit,
            &candidate,
            &["feature.txt"],
        );
        // Advance `main` past the authorized `previous_main` out from under
        // it -- exactly the scenario this whole gate exists to catch. Must
        // reach `remote`, not just this checkout's own local ref (round-7
        // review): `check_merge_ready` now fetches `main` fresh.
        git(
            dir.path(),
            &["update-ref", "refs/heads/main", &feature_commit],
        );
        push_main(dir.path(), &remote);
        let err = check_merge_ready(dir.path(), &remote, &state, &reviewer, &auth_id).unwrap_err();
        assert!(
            err.to_string()
                .contains("has advanced past authorized previous_main"),
            "{err}"
        );
    }

    /// The exact scenario `check_merge_ready`'s own doc comment describes:
    /// `main` genuinely advances on the shared remote, but *this* checkout
    /// (the one running `merge-ready`) never locally touches `refs/heads/
    /// main` itself -- a completely independent second checkout does the
    /// pushing. Before round 7's fix this passed `ready: true` regardless,
    /// since the local `main` this checkout started with was never fetched
    /// again; a genuine, unrelated fetch is what must catch it.
    #[test]
    fn rejects_main_advanced_only_on_the_remote_never_touched_by_this_checkout() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let (dir, _origin, remote, previous_main, feature_commit, candidate) =
            git_fixture(&author, &reviewer);
        let (state, auth_id) = state_with_authorization(
            &author,
            &reviewer,
            &previous_main,
            &feature_commit,
            &candidate,
            &["feature.txt"],
        );

        // A second, fully independent checkout pushes the advance -- `dir`
        // never runs a single git command against it. Its own new commit,
        // not `feature_commit` (which only exists in `dir`'s object
        // database, never pushed anywhere on its own).
        let second_checkout = tempfile::tempdir().unwrap();
        git(second_checkout.path(), &["clone", "--quiet", &remote, "."]);
        git(
            second_checkout.path(),
            &["config", "user.email", "other@example.com"],
        );
        git(second_checkout.path(), &["config", "user.name", "Other"]);
        std::fs::write(second_checkout.path().join("elsewhere.txt"), "x\n").unwrap();
        git(second_checkout.path(), &["add", "elsewhere.txt"]);
        git(
            second_checkout.path(),
            &["commit", "-q", "-m", "advance main from elsewhere"],
        );
        push_main(second_checkout.path(), &remote);

        let err = check_merge_ready(dir.path(), &remote, &state, &reviewer, &auth_id).unwrap_err();
        assert!(
            err.to_string()
                .contains("has advanced past authorized previous_main"),
            "{err}"
        );
    }

    #[test]
    fn rejects_a_hand_pushed_candidate_with_wrong_parents() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let (dir, _origin, remote, previous_main, feature_commit, _candidate) =
            git_fixture(&author, &reviewer);
        // Single-parent "candidate": parents = [feature], not
        // [previous_main, feature].
        let bad = commit_tree_with(
            dir.path(),
            &feature_commit,
            &[&feature_commit],
            "bad\n\nAgent-Bus-Reviewer: aiden",
        );
        let (state, auth_id) = state_with_authorization(
            &author,
            &reviewer,
            &previous_main,
            &feature_commit,
            &bad,
            &["feature.txt"],
        );
        let err = check_merge_ready(dir.path(), &remote, &state, &reviewer, &auth_id).unwrap_err();
        assert!(
            err.to_string().contains("candidate parents do not match"),
            "{err}"
        );
    }

    #[test]
    fn rejects_a_hand_pushed_candidate_missing_the_trailer() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let (dir, _origin, remote, previous_main, feature_commit, _candidate) =
            git_fixture(&author, &reviewer);
        let bad = commit_tree_with(
            dir.path(),
            &feature_commit,
            &[&previous_main, &feature_commit],
            "no trailer",
        );
        let (state, auth_id) = state_with_authorization(
            &author,
            &reviewer,
            &previous_main,
            &feature_commit,
            &bad,
            &["feature.txt"],
        );
        let err = check_merge_ready(dir.path(), &remote, &state, &reviewer, &auth_id).unwrap_err();
        assert!(
            err.to_string()
                .contains("exactly one matching Agent-Bus-Reviewer trailer"),
            "{err}"
        );
    }

    #[test]
    fn rejects_a_hand_pushed_candidate_with_the_wrong_reviewer_trailer_name() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let (dir, _origin, remote, previous_main, feature_commit, _candidate) =
            git_fixture(&author, &reviewer);
        // Right parents, exactly one Agent-Bus-Reviewer trailer -- but it
        // names a different agent than the reviewer running the check.
        let bad = commit_tree_with(
            dir.path(),
            &feature_commit,
            &[&previous_main, &feature_commit],
            "bad\n\nAgent-Bus-Reviewer: carol",
        );
        let (state, auth_id) = state_with_authorization(
            &author,
            &reviewer,
            &previous_main,
            &feature_commit,
            &bad,
            &["feature.txt"],
        );
        let err = check_merge_ready(dir.path(), &remote, &state, &reviewer, &auth_id).unwrap_err();
        assert!(
            err.to_string()
                .contains("exactly one matching Agent-Bus-Reviewer trailer"),
            "{err}"
        );
    }

    #[test]
    fn rejects_a_changed_path_outside_reviewed_scope() {
        let author = a("zoe");
        let reviewer = a("aiden");
        let dir = init_repo();
        let path = dir.path();
        let origin = init_bare_origin();
        let remote = origin.path().to_string_lossy().to_string();
        push_main(path, &remote);
        let previous_main = rev_parse(path, "main");
        // Detached, like `git_fixture` -- `main` must stay at `previous_main`.
        git(path, &["checkout", "--quiet", "--detach", &previous_main]);
        // Touches both feature.txt (in scope) and sneaky.txt (not).
        std::fs::write(path.join("feature.txt"), "feature content\n").unwrap();
        std::fs::write(path.join("sneaky.txt"), "sneaky content\n").unwrap();
        git(path, &["add", "."]);
        git(
            path,
            &[
                "commit",
                "-q",
                "-m",
                &format!("add feature\n\nAgent-Bus-Agent: {author}"),
            ],
        );
        let feature_commit = rev_parse(path, "HEAD");
        git(path, &["checkout", "--quiet", "main"]);
        let candidate = crate::merge_candidate::reconstruct_candidate(
            path,
            &previous_main,
            &feature_commit,
            &reviewer,
        )
        .unwrap();

        // review_scope only ever names feature.txt -- `check_merge_ready`'s
        // own diff check is what must catch the sneaky.txt leak (nothing
        // upstream of it inspects changed paths at all).
        let (state, auth_id) = state_with_authorization(
            &author,
            &reviewer,
            &previous_main,
            &feature_commit,
            &candidate,
            &["feature.txt"],
        );

        let err = check_merge_ready(dir.path(), &remote, &state, &reviewer, &auth_id).unwrap_err();
        assert!(
            err.to_string().contains("is outside reviewed_scope"),
            "{err}"
        );
    }

    // ------------------------------------------------------------ path_in_claim

    #[test]
    fn path_in_claim_matches_an_exact_claim() {
        assert!(path_in_claim("a/b.txt", &path_claim("a/b.txt")));
        assert!(!path_in_claim("a/c.txt", &path_claim("a/b.txt")));
    }

    #[test]
    fn path_in_claim_matches_a_directory_prefix_claim() {
        assert!(path_in_claim("a/b/c.txt", &path_claim("a/b/**")));
        assert!(path_in_claim("a/b", &path_claim("a/b/**")));
        assert!(!path_in_claim("a/bc.txt", &path_claim("a/b/**")));
        assert!(!path_in_claim("a/other/c.txt", &path_claim("a/b/**")));
    }
}
