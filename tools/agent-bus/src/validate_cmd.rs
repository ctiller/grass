//! `agent-bus validate` (AGENT_BUS.md section 9).

use crate::bus::BusCtx;
use crate::error::{invalid, AbResult};
use crate::scalars::Agent;
use serde_json::Value;

pub fn validate(
    ctx: &BusCtx,
    incremental: Option<&str>,
    linked: bool,
    quarantine_invalid: bool,
    json: bool,
) -> AbResult<()> {
    let result = match incremental {
        Some(range) => validate_incremental(ctx, range, linked),
        None => validate_full(ctx, linked),
    };

    match result {
        Ok(summary) => {
            if json {
                println!("{}", serde_json::to_string_pretty(&summary)?);
            } else {
                println!(
                    "valid: {} commits, {} agents",
                    summary["commits"], summary["agents"]
                );
            }
            Ok(())
        }
        Err(e) if quarantine_invalid => {
            let summary = quarantine_scan(ctx, &e.to_string())?;
            if json {
                println!("{}", serde_json::to_string_pretty(&summary)?);
            } else {
                println!("state_incomplete: {}", summary);
            }
            Ok(())
        }
        Err(e) => Err(e),
    }
}

fn validate_full(ctx: &BusCtx, linked: bool) -> AbResult<Value> {
    // Repair-commit content/authority validity (section 11's sole
    // append-only exception) is checked by `history::walk_full` itself now,
    // so every consumer gets it automatically, not just this command.
    let walk = crate::history::walk_full(&ctx.repo_root, crate::bus::BUS_BRANCH)?;
    let state = crate::apply::replay(&walk)?;
    let linked_report = if linked {
        Some(linked_validate(ctx, &state)?)
    } else {
        None
    };
    Ok(serde_json::json!({
        "schema_version": crate::envelope::SCHEMA_VERSION,
        "schema_kinds": crate::events::EventData::all_kinds().len(),
        "commits": walk.commits.len(),
        "agents": state.agents.len(),
        "issues": state.issues.len(),
        "dependencies": state.dependencies.len(),
        "handoffs": state.handoffs.len(),
        "reviews": state.reviews.len(),
        "linked": linked_report,
    }))
}

fn validate_incremental(ctx: &BusCtx, range: &str, linked: bool) -> AbResult<Value> {
    let (old, new) = range
        .split_once("..")
        .ok_or_else(|| invalid("--incremental expects <old>..<new>"))?;
    let base = ctx.load_state_at(old)?;
    let seed = base
        .agents
        .iter()
        .map(|(a, s)| (a.clone(), s.next_seq))
        .collect();
    let bus_json = ctx.bus_json()?;
    let commits =
        crate::history::walk_incremental(&ctx.repo_root, old, new, seed, &bus_json.coordinators)?;
    let state = crate::apply::replay_onto(base, &commits)?;
    let linked_report = if linked {
        Some(linked_validate(ctx, &state)?)
    } else {
        None
    };
    Ok(serde_json::json!({
        "commits": commits.len(),
        "agents": state.agents.len(),
        "linked": linked_report,
    }))
}

/// AGENT_BUS_SCHEMA.md section 9 (2026-09 update): "Linked validation fetches
/// exact product commits and candidate tags referenced by new events... A
/// present object that mismatches its claim is `invalid`. A remote outage,
/// unavailable remote, or absent object is `unverifiable`." This checks every
/// `review.merge_authorized` event's candidate tag/parents/tree/message
/// against local git objects (fetching from `origin` first when configured);
/// it does not yet fetch a *separate* product remote, so "unverifiable" here
/// means "not found in this local repository" rather than a distinct network
/// round trip.
fn linked_validate(ctx: &BusCtx, state: &crate::state::BusState) -> AbResult<Value> {
    let repo = &ctx.repo_root;
    if ctx.has_origin {
        let _ = crate::gitrepo::run(repo, &["fetch", "origin", "--tags"]);
    }
    let mut invalid_items = Vec::new();
    let mut unverifiable = Vec::new();
    for env in state.events.values() {
        let auth = match env.typed_data()? {
            crate::events::EventData::ReviewMergeAuthorized(d) => d,
            _ => continue,
        };
        let tag = format!("agent-candidate/{}/{}", env.agent, auth.candidate);
        let candidate_exists =
            crate::gitrepo::rev_parse_opt(repo, &format!("refs/tags/{tag}"))?.is_some();
        if !candidate_exists {
            unverifiable.push(serde_json::json!({"event": env.id.to_string(), "missing": format!("refs/tags/{tag}")}));
            continue;
        }
        let parents = crate::gitrepo::parents_of(repo, auth.candidate.as_str())?;
        if parents
            != vec![
                auth.previous_main.as_str().to_string(),
                auth.reviewed_commit.as_str().to_string(),
            ]
        {
            invalid_items.push(serde_json::json!({
                "event": env.id.to_string(),
                "problem": "candidate parents do not match previous_main/reviewed_commit",
            }));
            continue;
        }
        let trailers = crate::gitrepo::commit_message_trailers(repo, auth.candidate.as_str())?;
        let reviewer_trailers: Vec<&(String, String)> = trailers
            .iter()
            .filter(|(k, _)| k == "Agent-Bus-Reviewer")
            .collect();
        if reviewer_trailers.len() != 1 || reviewer_trailers[0].1 != env.agent.as_str() {
            invalid_items.push(serde_json::json!({
                "event": env.id.to_string(),
                "problem": "candidate does not have exactly one matching Agent-Bus-Reviewer trailer",
            }));
            continue;
        }

        // Merge-engine reconstruction: independently rebuild the candidate
        // from previous_main/reviewed_commit/reviewer and require a
        // byte-exact match, exactly like `review authorize` does at
        // publication time — this is what catches a `review.merge_authorized`
        // line appended by a direct push that bypassed `authorize` entirely.
        let objects_present = crate::gitrepo::rev_parse_opt(repo, auth.previous_main.as_str())?
            .is_some()
            && crate::gitrepo::rev_parse_opt(repo, auth.reviewed_commit.as_str())?.is_some();
        if !objects_present {
            unverifiable.push(serde_json::json!({
                "event": env.id.to_string(),
                "missing": "previous_main or reviewed_commit not fetchable locally",
            }));
            continue;
        }
        let chain = state.review_chain(&auth.nomination);
        let expected_authors: std::collections::BTreeSet<crate::scalars::Agent> = match chain {
            Some(c) => c.current_request.authors.iter().cloned().collect(),
            None => {
                invalid_items.push(serde_json::json!({
                    "event": env.id.to_string(),
                    "problem": "authorization's nomination is unknown",
                }));
                continue;
            }
        };
        if let Err(e) = crate::review_cmds::verify_authorship(
            repo,
            &env.agent,
            &expected_authors,
            auth.previous_main.as_str(),
            auth.reviewed_commit.as_str(),
        ) {
            invalid_items.push(serde_json::json!({"event": env.id.to_string(), "problem": format!("authorship: {e}")}));
            continue;
        }
        match crate::review_cmds::reconstruct_candidate(
            repo,
            auth.previous_main.as_str(),
            auth.reviewed_commit.as_str(),
            &env.agent,
        ) {
            Ok(reconstructed) if reconstructed == auth.candidate.as_str() => {}
            Ok(reconstructed) => {
                invalid_items.push(serde_json::json!({
                    "event": env.id.to_string(),
                    "problem": format!("candidate {} does not match reconstruction {reconstructed}", auth.candidate),
                }));
            }
            Err(e) => {
                invalid_items.push(serde_json::json!({"event": env.id.to_string(), "problem": format!("reconstruction: {e}")}));
            }
        }
    }
    Ok(serde_json::json!({
        "invalid": invalid_items,
        "unverifiable": unverifiable,
    }))
}

fn quarantine_scan(ctx: &BusCtx, reason: &str) -> AbResult<Value> {
    let agents = crate::storage::list_agents(&worktree_snapshot(ctx)?)?;
    let mut quarantined = Vec::new();
    let mut valid = Vec::new();
    for a in agents {
        match validate_one_agent(ctx, &a) {
            Ok(()) => valid.push(a.to_string()),
            Err(e) => quarantined
                .push(serde_json::json!({"agent": a.to_string(), "error": e.to_string()})),
        }
    }
    Ok(serde_json::json!({
        "state_incomplete": true,
        "full_validation_error": reason,
        "quarantined": quarantined,
        "valid_agents": valid,
    }))
}

fn validate_one_agent(ctx: &BusCtx, agent: &Agent) -> AbResult<()> {
    let dir = worktree_snapshot(ctx)?;
    crate::storage::read_agent_log(&dir, agent)?;
    Ok(())
}

/// A read-only checkout of the current `agent-bus` tip, for quarantine-mode
/// per-agent structural scanning (which needs plain files on disk).
fn worktree_snapshot(ctx: &BusCtx) -> AbResult<std::path::PathBuf> {
    let path = ctx.worktrees_root()?.join("_validate_snapshot");
    if path.exists() {
        crate::gitrepo::run_ok(
            &path,
            &[
                "fetch",
                ctx.repo_root.to_string_lossy().as_ref(),
                crate::bus::BUS_BRANCH,
            ],
        )?;
        let tip = crate::gitrepo::rev_parse(&ctx.repo_root, crate::bus::BUS_BRANCH)?;
        crate::gitrepo::checkout_detach(&path, &tip)?;
    } else {
        crate::gitrepo::ensure_bus_worktree(&ctx.repo_root, &path, crate::bus::BUS_BRANCH)?;
    }
    Ok(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bootstrap::BusJson;
    use crate::envelope::Envelope;
    use crate::events::{EventData, ReviewMergeAuthorized, ReviewRequest, Role};
    use crate::gitrepo::mock::MockGit;
    use crate::gitrepo::GitOutput;
    use crate::scalars::{Branch, EventId, ObjectId, PathClaim, StringSet, Text};
    use crate::state::{BusState, ItemStatus, ReviewChain};
    use crate::test_support::*;
    use std::collections::{BTreeMap, BTreeSet};
    use std::path::PathBuf;

    // --------------------------------------------------------------- pure
    // `linked_validate` takes an already-built `&BusState` and a `&BusCtx`;
    // every git call it (and `review_cmds::verify_authorship`/
    // `reconstruct_candidate`, which it delegates to) makes funnels through
    // `gitrepo::run`/`run_stdin`, so most of its branches are reachable with
    // a hand-built state and a scripted `MockGit`, no real repository at all.
    // The one exception is the byte-exact reconstruction path, which ends in
    // a real (unmockable) `git commit-tree` call — see the real-repo section
    // below for that scenario.

    fn fake_ctx() -> BusCtx {
        BusCtx {
            repo_root: PathBuf::from("fake-repo"),
            has_origin: false,
        }
    }

    fn empty_state() -> BusState {
        let bus_json = BusJson::new("sha1".to_string(), vec![a("coord1")], oid(999)).unwrap();
        BusState::new(bus_json)
    }

    /// Inserts a minimal accepted review chain for `nomination` (authors
    /// `authors`, reviewer `reviewer`) directly into `state`, bypassing
    /// `apply::replay` entirely — every field on `ReviewChain`/`BusState` is
    /// `pub`, so a unit test can just build the state it needs.
    fn insert_chain(
        state: &mut BusState,
        nomination: &EventId,
        authors: Vec<Agent>,
        reviewer: &Agent,
    ) {
        let request = ReviewRequest {
            authors: StringSet::from_iter(authors),
            product_branch: Branch::parse("refs/heads/agent/alice/feature".to_string()).unwrap(),
            reviewer: reviewer.clone(),
            required_checks: vec![],
            review_scope: StringSet::from_iter(vec![
                PathClaim::parse("feature.txt".to_string()).unwrap()
            ]),
            summary: Text::parse("s".into()).unwrap(),
            target_branch: Branch::parse("refs/heads/main".to_string()).unwrap(),
            evidence: StringSet::default(),
        };
        let mut nomination_reviewer = BTreeMap::new();
        nomination_reviewer.insert(nomination.clone(), reviewer.clone());
        let mut accepted_nominations = BTreeSet::new();
        accepted_nominations.insert(nomination.clone());
        state.reviews.insert(
            nomination.clone(),
            ReviewChain {
                root: nomination.clone(),
                nomination_events: vec![nomination.clone()],
                current_nomination: nomination.clone(),
                current_request: request,
                nomination_reviewer,
                accepted_nominations,
                decline_or_withdraw_or_reassign_status: ItemStatus::Open,
                findings: BTreeMap::new(),
                authorizations: vec![],
                merged: vec![],
                reconciled: vec![],
            },
        );
        state
            .review_chain_by_nomination
            .insert(nomination.clone(), nomination.clone());
    }

    fn insert_authorization(
        state: &mut BusState,
        reviewer: &Agent,
        seq: u64,
        auth: ReviewMergeAuthorized,
    ) {
        let env = Envelope::new(
            reviewer,
            seq,
            None,
            &EventData::ReviewMergeAuthorized(auth),
            [],
        );
        state.events.insert(env.id.clone(), env);
    }

    fn sample_auth(
        nomination: &EventId,
        previous_main: &str,
        reviewed_commit: &str,
        candidate: &str,
    ) -> ReviewMergeAuthorized {
        ReviewMergeAuthorized {
            nomination: nomination.clone(),
            product_branch: Branch::parse("refs/heads/agent/alice/feature".to_string()).unwrap(),
            previous_main: ObjectId::parse(previous_main.to_string()).unwrap(),
            reviewed_commit: ObjectId::parse(reviewed_commit.to_string()).unwrap(),
            candidate: ObjectId::parse(candidate.to_string()).unwrap(),
            merge_engine_epoch: EventId::parse("coord1:0".to_string()).unwrap(),
            checks: vec![],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter(vec![
                PathClaim::parse("feature.txt".to_string()).unwrap()
            ]),
            limitations: vec![],
            summary: Text::parse("s".into()).unwrap(),
        }
    }

    /// Generic `interpret-trailers --parse` responder: echoes back whatever
    /// `Key: value`-shaped lines were piped in via the preceding `show -s
    /// --format=%B` mock, mirroring real git's trailer extraction closely
    /// enough for these tests (every body here is hand-built to already look
    /// like a trailer block).
    fn generic_interpret_trailers(mock: MockGit) -> MockGit {
        mock.on_with(
            |_, a: &[&str], _| a == ["interpret-trailers", "--parse"],
            |_, _, stdin: Option<&str>| {
                let body = stdin.unwrap_or("");
                let lines: Vec<&str> = body.lines().filter(|l| l.contains(": ")).collect();
                Ok(GitOutput::ok(lines.join("\n")))
            },
        )
    }

    #[test]
    fn linked_validate_tag_missing_is_unverifiable() {
        let bob = a("bob");
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let mut state = empty_state();
        insert_chain(&mut state, &nomination, vec![a("alice")], &bob);
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let _guard = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::err(""),
            )
            .install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        assert_eq!(result["invalid"].as_array().unwrap().len(), 0);
        let unverifiable = result["unverifiable"].as_array().unwrap();
        assert_eq!(unverifiable.len(), 1);
        assert!(unverifiable[0]["missing"].as_str().unwrap().contains(&tag));
    }

    #[test]
    fn linked_validate_parents_mismatch_is_invalid() {
        let bob = a("bob");
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let mut state = empty_state();
        insert_chain(&mut state, &nomination, vec![a("alice")], &bob);
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let _guard = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::ok(candidate.clone()),
            )
            .on(
                &["show", "-s", "--format=%P", &candidate],
                GitOutput::ok(format!("{} {}", hash(9), reviewed)),
            )
            .install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        let invalid = result["invalid"].as_array().unwrap();
        assert_eq!(invalid.len(), 1);
        assert!(invalid[0]["problem"]
            .as_str()
            .unwrap()
            .contains("candidate parents do not match"));
        assert_eq!(result["unverifiable"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn linked_validate_missing_reviewer_trailer_is_invalid() {
        let bob = a("bob");
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let mut state = empty_state();
        insert_chain(&mut state, &nomination, vec![a("alice")], &bob);
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let mut mock = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::ok(candidate.clone()),
            )
            .on(
                &["show", "-s", "--format=%P", &candidate],
                GitOutput::ok(format!("{prev} {reviewed}")),
            )
            .on(
                &["show", "-s", "--format=%B", &candidate],
                GitOutput::ok("candidate commit, no trailer".to_string()),
            );
        mock = generic_interpret_trailers(mock);
        let _guard = mock.install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        let invalid = result["invalid"].as_array().unwrap();
        assert_eq!(invalid.len(), 1);
        assert!(invalid[0]["problem"]
            .as_str()
            .unwrap()
            .contains("does not have exactly one matching Agent-Bus-Reviewer trailer"));
    }

    #[test]
    fn linked_validate_wrong_reviewer_trailer_name_is_invalid() {
        // Exactly one Agent-Bus-Reviewer trailer (so the `len() != 1` half of
        // the check is satisfied) but it names a different agent than the one
        // (`env.agent`) who actually published this review.merge_authorized
        // event. `linked_validate_missing_reviewer_trailer_is_invalid` only
        // covers the zero-trailers case; this covers the other half of that
        // check's `||` so a bug that dropped the identity comparison
        // (accepting any single trailer, regardless of name) would be caught.
        let bob = a("bob");
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let mut state = empty_state();
        insert_chain(&mut state, &nomination, vec![a("alice")], &bob);
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let mut mock = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::ok(candidate.clone()),
            )
            .on(
                &["show", "-s", "--format=%P", &candidate],
                GitOutput::ok(format!("{prev} {reviewed}")),
            )
            .on(
                &["show", "-s", "--format=%B", &candidate],
                GitOutput::ok("candidate\n\nAgent-Bus-Reviewer: mallory".to_string()),
            );
        mock = generic_interpret_trailers(mock);
        let _guard = mock.install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        let invalid = result["invalid"].as_array().unwrap();
        assert_eq!(invalid.len(), 1);
        assert!(invalid[0]["problem"]
            .as_str()
            .unwrap()
            .contains("does not have exactly one matching Agent-Bus-Reviewer trailer"));
    }

    #[test]
    fn linked_validate_objects_not_fetchable_is_unverifiable() {
        let bob = a("bob");
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let mut state = empty_state();
        insert_chain(&mut state, &nomination, vec![a("alice")], &bob);
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let mut mock = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::ok(candidate.clone()),
            )
            .on(
                &["show", "-s", "--format=%P", &candidate],
                GitOutput::ok(format!("{prev} {reviewed}")),
            )
            .on(
                &["show", "-s", "--format=%B", &candidate],
                GitOutput::ok("candidate\n\nAgent-Bus-Reviewer: bob"),
            )
            // previous_main is fetchable, reviewed_commit is not.
            .on(
                &["rev-parse", "--verify", "--quiet", &prev],
                GitOutput::ok(prev.clone()),
            )
            .on(
                &["rev-parse", "--verify", "--quiet", &reviewed],
                GitOutput::err(""),
            );
        mock = generic_interpret_trailers(mock);
        let _guard = mock.install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        assert_eq!(result["invalid"].as_array().unwrap().len(), 0);
        let unverifiable = result["unverifiable"].as_array().unwrap();
        assert_eq!(unverifiable.len(), 1);
        assert!(unverifiable[0]["missing"]
            .as_str()
            .unwrap()
            .contains("not fetchable locally"));
    }

    #[test]
    fn linked_validate_unknown_nomination_is_invalid() {
        let bob = a("bob");
        // No matching nomination is ever inserted into `state.reviews`.
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let mut state = empty_state();
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let mut mock = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::ok(candidate.clone()),
            )
            .on(
                &["show", "-s", "--format=%P", &candidate],
                GitOutput::ok(format!("{prev} {reviewed}")),
            )
            .on(
                &["show", "-s", "--format=%B", &candidate],
                GitOutput::ok("candidate\n\nAgent-Bus-Reviewer: bob".to_string()),
            )
            .on(
                &["rev-parse", "--verify", "--quiet", &prev],
                GitOutput::ok(prev.clone()),
            )
            .on(
                &["rev-parse", "--verify", "--quiet", &reviewed],
                GitOutput::ok(reviewed.clone()),
            );
        mock = generic_interpret_trailers(mock);
        let _guard = mock.install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        let invalid = result["invalid"].as_array().unwrap();
        assert_eq!(invalid.len(), 1);
        assert!(invalid[0]["problem"]
            .as_str()
            .unwrap()
            .contains("authorization's nomination is unknown"));
    }

    #[test]
    fn linked_validate_authorship_failure_is_invalid() {
        let bob = a("bob");
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let introduced = hash(4);
        let mut state = empty_state();
        insert_chain(&mut state, &nomination, vec![a("alice")], &bob);
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let range = format!("{prev}..{reviewed}");
        let mut mock = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::ok(candidate.clone()),
            )
            .on(
                &["show", "-s", "--format=%P", &candidate],
                GitOutput::ok(format!("{prev} {reviewed}")),
            )
            .on(
                &["show", "-s", "--format=%B", &candidate],
                GitOutput::ok("candidate\n\nAgent-Bus-Reviewer: bob".to_string()),
            )
            .on(
                &["rev-parse", "--verify", "--quiet", &prev],
                GitOutput::ok(prev.clone()),
            )
            .on(
                &["rev-parse", "--verify", "--quiet", &reviewed],
                GitOutput::ok(reviewed.clone()),
            )
            .on(&["rev-list", &range], GitOutput::ok(introduced.clone()))
            // The lone introduced commit is authored by bob — the reviewer
            // himself — which `verify_authorship` must refuse.
            .on(
                &["show", "-s", "--format=%B", &introduced],
                GitOutput::ok("work\n\nAgent-Bus-Agent: bob".to_string()),
            );
        mock = generic_interpret_trailers(mock);
        let _guard = mock.install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        let invalid = result["invalid"].as_array().unwrap();
        assert_eq!(invalid.len(), 1);
        let problem = invalid[0]["problem"].as_str().unwrap();
        assert!(problem.starts_with("authorship:"), "{problem}");
        assert!(problem.contains("ineligible to merge"), "{problem}");
    }

    #[test]
    fn linked_validate_reconstruction_error_is_invalid() {
        let bob = a("bob");
        let nomination = EventId::parse("alice:2".to_string()).unwrap();
        let (prev, reviewed, candidate) = (hash(1), hash(2), hash(3));
        let introduced = hash(4);
        let mut state = empty_state();
        insert_chain(&mut state, &nomination, vec![a("alice")], &bob);
        insert_authorization(
            &mut state,
            &bob,
            2,
            sample_auth(&nomination, &prev, &reviewed, &candidate),
        );

        let tag = format!("refs/tags/agent-candidate/bob/{candidate}");
        let range = format!("{prev}..{reviewed}");
        let mut mock = MockGit::new()
            .on(
                &["rev-parse", "--verify", "--quiet", &tag],
                GitOutput::ok(candidate.clone()),
            )
            .on(
                &["show", "-s", "--format=%P", &candidate],
                GitOutput::ok(format!("{prev} {reviewed}")),
            )
            .on(
                &["show", "-s", "--format=%B", &candidate],
                GitOutput::ok("candidate\n\nAgent-Bus-Reviewer: bob".to_string()),
            )
            .on(
                &["rev-parse", "--verify", "--quiet", &prev],
                GitOutput::ok(prev.clone()),
            )
            .on(
                &["rev-parse", "--verify", "--quiet", &reviewed],
                GitOutput::ok(reviewed.clone()),
            )
            .on(&["rev-list", &range], GitOutput::ok(introduced.clone()))
            .on(
                &["show", "-s", "--format=%B", &introduced],
                GitOutput::ok("work\n\nAgent-Bus-Agent: alice".to_string()),
            )
            // Two merge bases: `reconstruct_candidate` must refuse before
            // ever attempting `merge-tree`/`commit-tree`.
            .on(
                &["merge-base", "--all", &prev, &reviewed],
                GitOutput::ok(format!("{}\n{}", hash(5), hash(6))),
            );
        mock = generic_interpret_trailers(mock);
        let _guard = mock.install();

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        let invalid = result["invalid"].as_array().unwrap();
        assert_eq!(invalid.len(), 1);
        let problem = invalid[0]["problem"].as_str().unwrap();
        assert!(problem.starts_with("reconstruction:"), "{problem}");
        assert!(
            problem.contains("do not have exactly one merge base"),
            "{problem}"
        );
    }

    #[test]
    fn linked_validate_ignores_non_authorization_events() {
        // A registration event (or any non-`review.merge_authorized` kind)
        // must simply be skipped, not treated as invalid/unverifiable.
        let coord = a("coord1");
        let mut state = empty_state();
        let data = EventData::AgentRegistered(crate::events::AgentRegistered {
            display_name: crate::scalars::Short::parse("coord1".into()).unwrap(),
            primary_role: Role::Coordinator,
            purpose: Text::parse("x".into()).unwrap(),
            product_base: None,
            product_branch: None,
            provider: None,
            model: None,
        });
        let env = Envelope::new(&coord, 0, None, &data, []);
        state.events.insert(env.id.clone(), env);

        let result = linked_validate(&fake_ctx(), &state).unwrap();
        assert_eq!(result["invalid"].as_array().unwrap().len(), 0);
        assert_eq!(result["unverifiable"].as_array().unwrap().len(), 0);
    }

    // --------------------------------------------------------- real-repo
    // The byte-exact reconstruction path ends in a real `git commit-tree`
    // call (`gitrepo::commit_tree_deterministic` shells out directly, not
    // through the mockable `gitrepo::run`), so producing a *correctly*
    // reconstructed-but-different candidate needs a real repository. Other
    // higher-level entry points here (`validate_incremental`,
    // `quarantine_scan`) also need one, since they go through
    // `BusCtx::load_state`/`history::walk_full`, which likewise bypasses the
    // mock at `history::blob_bytes`.

    #[test]
    fn linked_validate_byte_exact_mismatch_is_invalid_with_reconstructed_hash() {
        let dir = init_repo();
        let path = dir.path().to_path_buf();
        let ctx = bootstrap(&path, &["coord1"]);
        let alice = register(&ctx, "alice", Role::Implementor);
        let bob = register(&ctx, "bob", Role::Reviewer);
        let previous_main = git(&path, &["rev-parse", "main"]);
        let feature = author_commit(&path, &previous_main, "feature.txt", "content\n", "alice");
        git(&path, &["checkout", "--quiet", "main"]);
        let nomination = nominate(
            &ctx,
            &alice,
            &bob,
            "refs/heads/agent/alice/feature",
            &["feature.txt"],
            &["build"],
        );
        take(&ctx, &bob, &nomination);
        let mut state = ctx.load_state().unwrap();

        // A structurally-plausible but not byte-exact candidate: correct
        // parents and trailer, wrong message/identity/date (a plain `git
        // commit-tree` here, not the crate's deterministic constructor).
        let tree = git(&path, &["rev-parse", &format!("{feature}^{{tree}}")]);
        let wrong_candidate = git(
            &path,
            &[
                "commit-tree",
                &tree,
                "-p",
                &previous_main,
                "-p",
                &feature,
                "-m",
                "hand-built\n\nAgent-Bus-Reviewer: bob",
            ],
        );
        git(
            &path,
            &[
                "tag",
                &format!("agent-candidate/bob/{wrong_candidate}"),
                &wrong_candidate,
            ],
        );

        let auth = sample_auth(&nomination, &previous_main, &feature, &wrong_candidate);
        insert_authorization(&mut state, &bob, 2, auth);

        let result = linked_validate(&ctx, &state).unwrap();
        let invalid = result["invalid"].as_array().unwrap();
        assert_eq!(invalid.len(), 1, "{invalid:?}");
        let problem = invalid[0]["problem"].as_str().unwrap();
        assert!(
            problem.contains(&format!(
                "candidate {wrong_candidate} does not match reconstruction"
            )),
            "{problem}"
        );
    }

    #[test]
    fn validate_incremental_reports_new_commits_and_agents() {
        let dir = init_repo();
        let path = dir.path().to_path_buf();
        let ctx = bootstrap(&path, &["coord1"]);
        let old_tip = git(&path, &["rev-parse", "refs/heads/agent-bus"]);
        let _alice = register(&ctx, "alice", Role::Implementor);
        let new_tip = git(&path, &["rev-parse", "refs/heads/agent-bus"]);
        let range = format!("{old_tip}..{new_tip}");

        let result = validate_incremental(&ctx, &range, false).unwrap();
        assert_eq!(result["commits"], 1);
        assert_eq!(result["agents"], 2);
        assert!(result["linked"].is_null());

        // The top-level dispatcher's `Some(range) => validate_incremental`
        // arm is otherwise never exercised (`tests/cli_flow.rs` only calls
        // full, non-incremental `validate`).
        validate(&ctx, Some(&range), false, false, false)
            .expect("incremental validate via the CLI-level dispatcher");
    }

    #[test]
    fn validate_top_level_rejects_malformed_incremental_range() {
        let ctx = fake_ctx();
        let err = validate_incremental(&ctx, "not-a-range", false).unwrap_err();
        assert!(err.to_string().contains("expects <old>..<new>"), "{err}");
    }

    fn corrupt_alice_log(ctx: &BusCtx, alice_wt: &std::path::Path) {
        let tip = git(&ctx.repo_root, &["rev-parse", "refs/heads/agent-bus"]);
        git(alice_wt, &["checkout", "--quiet", "--detach", &tip]);
        let log_path = alice_wt.join("alice").join("000000.jsonl");
        let mut existing = std::fs::read_to_string(&log_path).unwrap();
        existing.push_str("not-json-at-all\n");
        std::fs::write(&log_path, existing).unwrap();
        git(alice_wt, &["add", "-A"]);
        git(
            alice_wt,
            &[
                "commit",
                "-q",
                "-m",
                "agent-bus: corrupt alice log for a quarantine test",
            ],
        );
        git(alice_wt, &["push", ".", "HEAD:refs/heads/agent-bus"]);
    }

    #[test]
    fn quarantine_scan_separates_valid_from_quarantined_agents() {
        let dir = init_repo();
        let path = dir.path().to_path_buf();
        let ctx = bootstrap(&path, &["coord1"]);
        let alice = register(&ctx, "alice", Role::Implementor);
        let _bob = register(&ctx, "bob", Role::Reviewer);
        let alice_wt = ctx.worktree_path(&alice).unwrap();
        corrupt_alice_log(&ctx, &alice_wt);

        // The full structural walk must now fail...
        assert!(crate::history::walk_full(&ctx.repo_root, crate::bus::BUS_BRANCH).is_err());

        // ...and the top-level `validate` dispatcher must catch that and
        // still succeed once `--quarantine-invalid` is set.
        validate(&ctx, None, false, true, false).expect("quarantine mode must itself succeed");

        let summary = quarantine_scan(&ctx, "boom").unwrap();
        let quarantined: Vec<String> = summary["quarantined"]
            .as_array()
            .unwrap()
            .iter()
            .map(|q| q["agent"].as_str().unwrap().to_string())
            .collect();
        assert_eq!(quarantined, vec!["alice".to_string()]);
        let valid: Vec<String> = summary["valid_agents"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap().to_string())
            .collect();
        assert!(valid.contains(&"coord1".to_string()), "{valid:?}");
        assert!(valid.contains(&"bob".to_string()), "{valid:?}");
        assert!(!valid.contains(&"alice".to_string()), "{valid:?}");
    }
}
