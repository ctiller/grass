//! Review/merge CLI commands (AGENT_REVIEW.md), including the git-dependent
//! cross-checks (candidate tags, authorship trailers, `main` history) that
//! `apply.rs` deliberately leaves out of pure bus-log replay.

use crate::bus::{self, BusCtx};
use crate::error::{invalid, AbResult};
use crate::events::*;
use crate::scalars::*;
use crate::state::FindingDisposition;
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::Path;

fn from_value<T: serde::de::DeserializeOwned>(v: Value) -> AbResult<T> {
    serde_json::from_value(v).map_err(|e| invalid(format!("invalid payload: {e}")))
}

pub fn nominate(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: ReviewNominated = from_value(v)?;
    let refs: Vec<EventId> = data.evidence.iter().cloned().collect();
    let env = bus::publish_event(ctx, &agent, EventData::ReviewNominated(data), refs)?;
    println!("nominated {}", env.id);
    Ok(())
}

pub fn take(ctx: &BusCtx, agent: &str, nomination: &str, note: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let nomination = EventId::parse(nomination.to_string())?;
    let data = EventData::ReviewNominationAccepted(ReviewNominationAccepted {
        nomination: nomination.clone(),
        note: Text::parse(note.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![nomination])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn decline(ctx: &BusCtx, agent: &str, nomination: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let nomination = EventId::parse(nomination.to_string())?;
    let data = EventData::ReviewNominationDeclined(ReviewNominationDeclined {
        nomination: nomination.clone(),
        reason: Text::parse(reason.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![nomination])?;
    println!("published {}", env.id);
    Ok(())
}

pub fn changes(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: ReviewChangesRequested = from_value(v)?;
    let mut refs = vec![data.nomination.clone()];
    refs.extend(data.evidence.iter().cloned());
    let env = bus::publish_event(ctx, &agent, EventData::ReviewChangesRequested(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

pub fn clear(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: ReviewFindingsCleared = from_value(v)?;
    let refs = vec![data.nomination.clone(), data.changes_event.clone()];
    let env = bus::publish_event(ctx, &agent, EventData::ReviewFindingsCleared(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

pub fn supersede(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: ReviewFindingsSuperseded = from_value(v)?;
    let refs = vec![data.nomination.clone(), data.changes_event.clone()];
    let env = bus::publish_event(ctx, &agent, EventData::ReviewFindingsSuperseded(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

pub fn reassign(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let mut v = bus::read_json_file(std::path::Path::new(file))?;
    let replaces = v
        .get("replaces")
        .and_then(|x| x.as_str())
        .ok_or_else(|| invalid("file must set \"replaces\""))?
        .to_string();
    let replaces_id = EventId::parse(replaces)?;
    let state = ctx.load_state()?;
    let chain = state
        .review_chain(&replaces_id)
        .ok_or_else(|| invalid(format!("unknown nomination {replaces_id}")))?;
    let inherited: Vec<Value> = chain
        .findings
        .iter()
        .filter(|(_, f)| f.disposition == FindingDisposition::Open)
        .map(|((ce, fid), _)| serde_json::json!({"changes_event": ce.to_string(), "finding_id": fid}))
        .collect();
    if let Value::Object(map) = &mut v {
        map.insert("inherited_findings".to_string(), Value::Array(inherited));
    }
    let data: ReviewReassigned = from_value(v)?;
    let mut refs = vec![data.replaces.clone()];
    for f in &data.inherited_findings {
        refs.push(f.changes_event.clone());
    }
    refs.extend(data.evidence.iter().cloned());
    let env = bus::publish_event(ctx, &agent, EventData::ReviewReassigned(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

pub fn withdraw(ctx: &BusCtx, agent: &str, nomination: &str, reason: &str) -> AbResult<()> {
    let agent = Agent::parse(agent.to_string())?;
    let nomination = EventId::parse(nomination.to_string())?;
    let data = EventData::ReviewWithdrawn(ReviewWithdrawn {
        nomination: nomination.clone(),
        reason: Text::parse(reason.to_string())?,
    });
    let env = bus::publish_event(ctx, &agent, data, vec![nomination])?;
    println!("published {}", env.id);
    Ok(())
}

fn commit_authors(repo: &Path, commit: &str) -> AbResult<BTreeSet<Agent>> {
    let trailers = crate::gitrepo::commit_message_trailers(repo, commit)?;
    let mut out = BTreeSet::new();
    for (k, v) in trailers {
        if k == "Agent-Bus-Agent" {
            out.insert(Agent::parse(v)?);
        }
    }
    Ok(out)
}

fn require_pinned_git_version() -> AbResult<()> {
    let installed = crate::gitrepo::version()?;
    if installed != crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION {
        return Err(invalid(format!(
            "installed git {installed} does not match the pinned merge engine version {}",
            crate::bootstrap::SUPPORTED_MERGE_ENGINE_VERSION
        )));
    }
    Ok(())
}

/// AGENT_REVIEW.md section 3/7: every commit introduced by `reviewed_commit`
/// over `previous_main` must carry an `Agent-Bus-Agent` trailer, the union of
/// those trailers must be exactly the nomination's `authors`, and `reviewer`
/// must not be among them. Returns the introduced commits (in `previous_main`
/// order) for callers that also need them.
pub(crate) fn verify_authorship(
    repo: &Path,
    reviewer: &Agent,
    expected_authors: &BTreeSet<Agent>,
    previous_main: &str,
    reviewed_commit: &str,
) -> AbResult<Vec<String>> {
    let introduced = crate::gitrepo::commits_between_first_parent_exclusive(repo, previous_main, reviewed_commit)?;
    if introduced.is_empty() {
        return Err(invalid("reviewed_commit introduces no content over previous_main"));
    }
    let mut authors = BTreeSet::new();
    for c in &introduced {
        let a = commit_authors(repo, c)?;
        if a.is_empty() {
            return Err(invalid(format!("commit {c} has no Agent-Bus-Agent trailer")));
        }
        if a.contains(reviewer) {
            return Err(invalid(format!("reviewer {reviewer} authored commit {c}; ineligible to merge")));
        }
        authors.extend(a);
    }
    if &authors != expected_authors {
        return Err(invalid(format!(
            "authors of introduced commits {authors:?} do not match nomination authors {expected_authors:?}"
        )));
    }
    Ok(introduced)
}

/// Deterministically reconstructs the exact candidate object id that
/// `prepare-merge` would produce for `(previous_main, reviewed_commit,
/// reviewer)` (AGENT_REVIEW.md section 7). Used both to construct a candidate
/// and, in `authorize`, to verify one claimed by a `review.merge_authorized`
/// payload without trusting anything the payload merely asserts.
pub(crate) fn reconstruct_candidate(
    repo: &Path,
    previous_main: &str,
    reviewed_commit: &str,
    reviewer: &Agent,
) -> AbResult<String> {
    if crate::gitrepo::merge_base_count(repo, previous_main, reviewed_commit)? != 1 {
        return Err(invalid("previous_main and reviewed_commit do not have exactly one merge base"));
    }
    let tree = crate::gitrepo::merge_tree_write_tree(repo, previous_main, reviewed_commit)?;
    let message = format!("agent-bus candidate\n\nAgent-Bus-Reviewer: {reviewer}\n");
    crate::gitrepo::commit_tree_deterministic(repo, &tree, &[previous_main, reviewed_commit], &message)
}

/// AGENT_REVIEW.md section 7: construct the no-conflict candidate merge
/// commit and publish its immutable candidate tag.
pub fn prepare_merge(ctx: &BusCtx, agent: &str, nomination: &str, reviewed_commit: &str) -> AbResult<()> {
    let reviewer = Agent::parse(agent.to_string())?;
    let nomination = EventId::parse(nomination.to_string())?;
    let reviewed_commit = ObjectId::parse(reviewed_commit.to_string())?;
    require_pinned_git_version()?;
    let state = ctx.load_state()?;
    let chain = state
        .review_chain(&nomination)
        .ok_or_else(|| invalid(format!("unknown nomination {nomination}")))?;
    if chain.current_nomination != nomination {
        return Err(invalid("nomination is no longer current"));
    }
    if !chain.accepted() || chain.current_request.reviewer != reviewer {
        return Err(invalid("only the accepting reviewer may prepare a merge"));
    }

    let repo = &ctx.repo_root;
    let previous_main = crate::gitrepo::rev_parse(repo, "refs/heads/main")?;
    let expected_authors: BTreeSet<Agent> = chain.current_request.authors.iter().cloned().collect();
    verify_authorship(repo, &reviewer, &expected_authors, &previous_main, reviewed_commit.as_str())?;

    let candidate = reconstruct_candidate(repo, &previous_main, reviewed_commit.as_str(), &reviewer)?;
    let tag = format!("agent-candidate/{reviewer}/{candidate}");
    crate::gitrepo::tag_lightweight(repo, &tag, &candidate)?;
    if ctx.has_origin {
        let _ = crate::gitrepo::run(repo, &["push", "origin", &format!("refs/tags/{tag}")]);
    }
    println!("candidate {candidate}");
    println!("previous_main {previous_main}");
    println!("merge_engine_epoch {}", state.current_merge_engine_epoch);
    Ok(())
}

pub fn authorize(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let reviewer = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: ReviewMergeAuthorized = from_value(v)?;
    require_pinned_git_version()?;

    let state = ctx.load_state()?;
    let chain = state
        .review_chain(&data.nomination)
        .ok_or_else(|| invalid(format!("unknown nomination {}", data.nomination)))?;

    let repo = &ctx.repo_root;
    // Finding-#3-class fix: these mechanical eligibility/authorship checks
    // used to live only in `prepare-merge`, a convenience the reviewer could
    // simply skip (nothing stopped hand-building the same candidate and
    // calling `authorize` directly). They are re-run here, at the actual
    // publication gate, so they cannot be bypassed.
    let expected_authors: BTreeSet<Agent> = chain.current_request.authors.iter().cloned().collect();
    verify_authorship(
        repo,
        &reviewer,
        &expected_authors,
        data.previous_main.as_str(),
        data.reviewed_commit.as_str(),
    )?;
    let reconstructed = reconstruct_candidate(repo, data.previous_main.as_str(), data.reviewed_commit.as_str(), &reviewer)?;
    if reconstructed != data.candidate.as_str() {
        return Err(invalid(format!(
            "candidate {} does not match the deterministic reconstruction {reconstructed} from previous_main/reviewed_commit/reviewer",
            data.candidate
        )));
    }
    if !crate::gitrepo::tag_exists_at(
        repo,
        &format!("agent-candidate/{reviewer}/{}", data.candidate),
        data.candidate.as_str(),
    )? {
        return Err(invalid("candidate tag is not fetchable before authorization"));
    }

    let mut refs = vec![data.nomination.clone(), data.merge_engine_epoch.clone()];
    for fd in &data.finding_dispositions {
        refs.push(fd.changes_event.clone());
    }
    refs.extend(data.evidence.iter().cloned());
    let env = bus::publish_event(ctx, &reviewer, EventData::ReviewMergeAuthorized(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

/// AGENT_REVIEW.md section 8 pre-merge gate.
pub fn merge_ready(ctx: &BusCtx, agent: &str, authorization: &str, json: bool) -> AbResult<()> {
    let reviewer = Agent::parse(agent.to_string())?;
    let authorization = EventId::parse(authorization.to_string())?;
    let state = ctx.load_state()?;
    let auth_env = state
        .events
        .get(&authorization)
        .ok_or_else(|| invalid(format!("unknown authorization {authorization}")))?;
    let auth: ReviewMergeAuthorized = match auth_env.typed_data()? {
        EventData::ReviewMergeAuthorized(d) => d,
        _ => return Err(invalid(format!("{authorization} is not a review.merge_authorized event"))),
    };
    if auth_env.agent != reviewer {
        return Err(invalid("authorization was not published by the given reviewer"));
    }
    let chain = state
        .review_chain(&auth.nomination)
        .ok_or_else(|| invalid("unknown nomination for this authorization"))?;
    if chain.current_request.reviewer != reviewer || !chain.accepted() {
        return Err(invalid("reviewer is not the accepted eligible reviewer for this nomination"));
    }
    for (_, f) in chain.findings.iter() {
        if f.disposition == FindingDisposition::Open {
            return Err(invalid(format!("finding {} has no terminal disposition", f.finding_id)));
        }
    }
    if let Some(blocking) = crate::apply::blocking_issue_for_chain(&state, chain) {
        return Err(invalid(format!("issue {blocking} explicitly blocks this nomination chain")));
    }
    if auth.reviewed_scope != chain.current_request.review_scope {
        return Err(invalid("authorization reviewed_scope does not exactly equal the nomination's review_scope"));
    }
    let repo = &ctx.repo_root;
    let current_main = crate::gitrepo::rev_parse(repo, "refs/heads/main")?;
    if current_main != auth.previous_main.as_str() {
        return Err(invalid(format!(
            "current main {current_main} has advanced past authorized previous_main {}",
            auth.previous_main
        )));
    }
    let parents = crate::gitrepo::parents_of(repo, auth.candidate.as_str())?;
    if parents != vec![auth.previous_main.as_str().to_string(), auth.reviewed_commit.as_str().to_string()] {
        return Err(invalid("candidate parents do not match previous_main/reviewed_commit in order"));
    }
    let trailers = crate::gitrepo::commit_message_trailers(repo, auth.candidate.as_str())?;
    let reviewer_trailers: Vec<&(String, String)> =
        trailers.iter().filter(|(k, _)| k == "Agent-Bus-Reviewer").collect();
    if reviewer_trailers.len() != 1 || reviewer_trailers[0].1 != reviewer.as_str() {
        return Err(invalid("candidate must have exactly one matching Agent-Bus-Reviewer trailer"));
    }
    let changed = crate::gitrepo::diff_name_status(repo, &current_main, auth.candidate.as_str())?;
    for (_, path) in &changed {
        if !auth.reviewed_scope.iter().any(|p| path_in_claim(path, p)) {
            return Err(invalid(format!("changed path {path} is outside reviewed_scope")));
        }
    }
    for c in &auth.checks {
        if c.result != crate::common::CheckOutcome::Passed {
            return Err(invalid("a required check result is not passed"));
        }
    }

    if json {
        println!("{}", serde_json::json!({"ready": true, "candidate": auth.candidate.as_str()}));
    } else {
        println!("merge-ready: {}", auth.candidate);
    }
    Ok(())
}

fn path_in_claim(path: &str, claim: &crate::scalars::PathClaim) -> bool {
    match claim.as_str().strip_suffix("/**") {
        Some(prefix) => path == prefix || path.starts_with(&format!("{prefix}/")),
        None => path == claim.as_str(),
    }
}

pub fn merged(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let reviewer = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: ReviewMerged = from_value(v)?;
    let repo = &ctx.repo_root;
    let parents = crate::gitrepo::parents_of(repo, data.main_commit.as_str())?;
    if parents.first().map(|s| s.as_str()) != Some(data.previous_main.as_str()) {
        return Err(invalid("main_commit's first parent does not match previous_main"));
    }
    let current_main = crate::gitrepo::rev_parse(repo, "refs/heads/main")?;
    if current_main != data.main_commit.as_str() {
        return Err(invalid("refs/heads/main does not currently equal main_commit"));
    }
    let refs = vec![data.authorization.clone()];
    let env = bus::publish_event(ctx, &reviewer, EventData::ReviewMerged(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

pub fn reconcile(ctx: &BusCtx, agent: &str, file: &str) -> AbResult<()> {
    let coordinator = Agent::parse(agent.to_string())?;
    let v = bus::read_json_file(std::path::Path::new(file))?;
    let data: ReviewMergeReconciled = from_value(v)?;
    let repo = &ctx.repo_root;
    let is_first_parent_of_main =
        crate::gitrepo::rev_list_first_parent(repo, data.previous_main.as_str(), "refs/heads/main")?
            .iter()
            .any(|c| c == data.main_commit.as_str());
    if !is_first_parent_of_main {
        return Err(invalid(
            "main_commit is not a first-parent successor of previous_main on current main",
        ));
    }
    let refs = vec![data.authorization.clone()];
    let env = bus::publish_event(ctx, &coordinator, EventData::ReviewMergeReconciled(data), refs)?;
    println!("published {}", env.id);
    Ok(())
}

/// Walks post-bootstrap first-parent `main` history, correlating every merge
/// with its bus authorization/receipt (AGENT_BUS_SCHEMA.md section 9). Unlike
/// a name-only correlation, this fetches the actual authorization event named
/// by trailers/receipts and compares its recorded `candidate`/`previous_main`
/// against the real commit before accepting it as a match, and verifies every
/// introduced commit's authorship trailers directly — so a hand-crafted merge
/// commit that merely carries a plausible `Agent-Bus-Reviewer` trailer cannot
/// pass as authorized.
pub fn audit_main(ctx: &BusCtx, to: Option<&str>, json: bool) -> AbResult<()> {
    let repo = &ctx.repo_root;
    let bus_json = ctx.bus_json()?;
    let to = to.unwrap_or("refs/heads/main").to_string();
    let state = ctx.load_state()?;

    let commits = crate::gitrepo::rev_list_first_parent(repo, bus_json.product_review_from.as_str(), &to)?;
    let mut findings = Vec::new();
    let mut previous = bus_json.product_review_from.as_str().to_string();
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
        let reviewer_trailers: Vec<&(String, String)> =
            trailers.iter().filter(|(k, _)| k == "Agent-Bus-Reviewer").collect();
        if reviewer_trailers.len() != 1 {
            findings.push(serde_json::json!({"commit": commit, "problem": "missing or duplicate Agent-Bus-Reviewer trailer"}));
            previous = commit;
            continue;
        }
        let reviewer_name = reviewer_trailers[0].1.clone();
        let reviewer = match Agent::parse(reviewer_name.clone()) {
            Ok(a) => a,
            Err(_) => {
                findings.push(serde_json::json!({"commit": commit, "problem": "Agent-Bus-Reviewer trailer is not a valid agent name"}));
                previous = commit;
                continue;
            }
        };
        if state.agents.get(&reviewer).map(|a| a.primary_role) != Some(Role::Reviewer) {
            findings.push(serde_json::json!({"commit": commit, "problem": "trailer names a non-reviewer identity", "reviewer": reviewer_name}));
        }

        let introduced_authors = match commit_authors_only(repo, &previous, &reviewed_commit) {
            Ok(a) => a,
            Err(e) => {
                findings.push(serde_json::json!({"commit": commit, "problem": format!("author trailer check failed: {e}")}));
                previous = commit;
                continue;
            }
        };
        if introduced_authors.contains(&reviewer) {
            findings.push(serde_json::json!({"commit": commit, "problem": "reviewer authored an introduced commit", "reviewer": reviewer_name}));
        }

        let matching_auth = state.reviews.values().find(|chain| {
            let authors_match =
                introduced_authors == chain.current_request.authors.iter().cloned().collect::<BTreeSet<Agent>>();
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
                findings.push(serde_json::json!({"commit": commit, "problem": "no review.merge_authorized matches this exact candidate/previous_main/reviewed_commit", "reviewer": reviewer_name}));
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
                    findings.push(serde_json::json!({"commit": commit, "problem": "missing review.merged/review.merge_reconciled receipt for this exact commit", "reviewer": reviewer_name}));
                }
            }
        }
        previous = commit;
    }

    if json {
        println!("{}", serde_json::to_string_pretty(&findings)?);
    } else if findings.is_empty() {
        println!("audit-main: clean");
    } else {
        for f in &findings {
            println!("{f}");
        }
    }
    Ok(())
}

fn commit_authors_only(repo: &Path, previous_main: &str, reviewed_commit: &str) -> AbResult<BTreeSet<Agent>> {
    let introduced = crate::gitrepo::commits_between_first_parent_exclusive(repo, previous_main, reviewed_commit)?;
    let mut authors = BTreeSet::new();
    for c in &introduced {
        let a = commit_authors(repo, c)?;
        if a.is_empty() {
            return Err(invalid(format!("commit {c} has no Agent-Bus-Agent trailer")));
        }
        authors.extend(a);
    }
    Ok(authors)
}
