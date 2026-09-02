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
                println!("valid: {} commits, {} agents", summary["commits"], summary["agents"]);
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
    let linked_report = if linked { Some(linked_validate(ctx, &state)?) } else { None };
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
    let seed = base.agents.iter().map(|(a, s)| (a.clone(), s.next_seq)).collect();
    let bus_json = ctx.bus_json()?;
    let commits = crate::history::walk_incremental(&ctx.repo_root, old, new, seed, &bus_json.coordinators)?;
    let state = crate::apply::replay_onto(base, &commits)?;
    let linked_report = if linked { Some(linked_validate(ctx, &state)?) } else { None };
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
        let candidate_exists = crate::gitrepo::rev_parse_opt(repo, &format!("refs/tags/{tag}"))?.is_some();
        if !candidate_exists {
            unverifiable.push(serde_json::json!({"event": env.id.to_string(), "missing": format!("refs/tags/{tag}")}));
            continue;
        }
        let parents = crate::gitrepo::parents_of(repo, auth.candidate.as_str())?;
        if parents != vec![auth.previous_main.as_str().to_string(), auth.reviewed_commit.as_str().to_string()] {
            invalid_items.push(serde_json::json!({
                "event": env.id.to_string(),
                "problem": "candidate parents do not match previous_main/reviewed_commit",
            }));
            continue;
        }
        let trailers = crate::gitrepo::commit_message_trailers(repo, auth.candidate.as_str())?;
        let reviewer_trailers: Vec<&(String, String)> =
            trailers.iter().filter(|(k, _)| k == "Agent-Bus-Reviewer").collect();
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
        let objects_present = crate::gitrepo::rev_parse_opt(repo, auth.previous_main.as_str())?.is_some()
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
            Err(e) => quarantined.push(serde_json::json!({"agent": a.to_string(), "error": e.to_string()})),
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
    let path = ctx.worktrees_root().join("_validate_snapshot");
    if path.exists() {
        crate::gitrepo::run_ok(&path, &["fetch", ctx.repo_root.to_string_lossy().as_ref(), crate::bus::BUS_BRANCH])?;
        let tip = crate::gitrepo::rev_parse(&ctx.repo_root, crate::bus::BUS_BRANCH)?;
        crate::gitrepo::checkout_detach(&path, &tip)?;
    } else {
        crate::gitrepo::ensure_bus_worktree(&ctx.repo_root, &path, crate::bus::BUS_BRANCH)?;
    }
    Ok(path)
}
