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
    // g-reviewer:4: a candidate whose tag never reached origin cannot be
    // fetched or verified by any other agent (or `--linked` validator) --
    // that must fail `prepare-merge` outright, not silently proceed to print
    // a `candidate` line the reviewer might go on to authorize anyway.
    if ctx.has_origin {
        let out = crate::gitrepo::run(repo, &["push", "origin", &format!("refs/tags/{tag}")])?;
        if !out.success {
            return Err(invalid(format!(
                "failed to publish candidate tag refs/tags/{tag} to origin: {}",
                out.stderr
            )));
        }
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
    let tag = format!("agent-candidate/{reviewer}/{}", data.candidate);
    if !crate::gitrepo::tag_exists_at(repo, &tag, data.candidate.as_str())? {
        return Err(invalid("candidate tag is not fetchable before authorization"));
    }
    // g-reviewer:4: local presence alone proves nothing about whether any
    // *other* agent (or a `--linked` validator elsewhere) can fetch this
    // candidate -- only origin can. Without this, a candidate tag that
    // failed to push (or was later deleted from origin) could still pass
    // authorization on the strength of the reviewer's own local clone.
    if ctx.has_origin && !crate::gitrepo::remote_tag_matches(repo, "origin", &tag, data.candidate.as_str())? {
        return Err(invalid(format!(
            "candidate tag refs/tags/{tag} is not fetchable from origin; other agents could not verify this merge"
        )));
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
    let findings = audit_main_findings(ctx, to)?;

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

/// The pure correlation walk behind `audit_main`, split out so unit tests can
/// inspect the findings directly instead of parsing `audit_main`'s printed
/// output.
fn audit_main_findings(ctx: &BusCtx, to: Option<&str>) -> AbResult<Vec<Value>> {
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

    Ok(findings)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gitrepo::mock::{MockGit, MockGuard};
    use crate::gitrepo::GitOutput;
    // `nominate`/`take` collide with this module's own CLI-level commands of
    // the same name, so pull those two in under different names.
    use crate::test_support::{
        a, author_commit, bootstrap, git, hash, init_repo, register, take as take_review, write_json,
    };
    use crate::test_support::nominate as nominate_review;
    use std::path::PathBuf;

    // ---------------------------------------------------------------- pure
    // `verify_authorship`/`reconstruct_candidate`/`path_in_claim` take an
    // explicit `repo: &Path` and make no filesystem assumptions about it, so
    // these are tested with a scripted `MockGit` and no real repository.

    /// Installs a MockGit answering `rev-list <previous_main>..<reviewed_commit>`
    /// with `commits` (newline-joined, in order), and for each commit the two
    /// calls `commit_message_trailers` always makes (`show -s --format=%B`
    /// then `interpret-trailers --parse`), reconstructing exactly the
    /// `Agent-Bus-Agent` trailers named in `trailer_agents` for that commit.
    fn mock_authorship(
        previous_main: &str,
        reviewed_commit: &str,
        commits: &[&str],
        trailer_agents: std::collections::BTreeMap<&str, Vec<&str>>,
    ) -> MockGuard {
        let range = format!("{previous_main}..{reviewed_commit}");
        let commits_out = commits.join("\n");
        let trailer_agents: std::collections::BTreeMap<String, Vec<String>> = trailer_agents
            .into_iter()
            .map(|(k, v)| (k.to_string(), v.into_iter().map(|s| s.to_string()).collect()))
            .collect();
        MockGit::new()
            .on(&["rev-list", &range], GitOutput::ok(commits_out))
            .on_with(
                |_, a: &[&str], _| a.first() == Some(&"show") && a.get(1) == Some(&"-s"),
                move |_, a: &[&str], _| {
                    let c = *a.last().unwrap();
                    let body = trailer_agents
                        .get(c)
                        .map(|agents| {
                            agents.iter().map(|ag| format!("Agent-Bus-Agent: {ag}")).collect::<Vec<_>>().join("\n")
                        })
                        .unwrap_or_default();
                    Ok(GitOutput::ok(format!("msg\n\n{body}")))
                },
            )
            .on_with(
                |_, a: &[&str], _| a == ["interpret-trailers", "--parse"],
                |_, _, stdin: Option<&str>| {
                    let body = stdin.unwrap_or("");
                    let lines: Vec<&str> = body.lines().filter(|l| l.contains(": ")).collect();
                    Ok(GitOutput::ok(lines.join("\n")))
                },
            )
            .install()
    }

    #[test]
    fn verify_authorship_rejects_empty_introduced_range() {
        let (prev, reviewed) = (hash(1), hash(2));
        let _guard = mock_authorship(&prev, &reviewed, &[], Default::default());
        let bob = a("bob");
        let err = verify_authorship(&PathBuf::from("."), &bob, &BTreeSet::new(), &prev, &reviewed).unwrap_err();
        assert!(err.to_string().contains("introduces no content"), "{err}");
    }

    #[test]
    fn verify_authorship_rejects_missing_author_trailer() {
        let (prev, reviewed) = (hash(1), hash(2));
        let c = hash(3);
        let _guard = mock_authorship(&prev, &reviewed, &[&c], Default::default());
        let bob = a("bob");
        let err = verify_authorship(&PathBuf::from("."), &bob, &BTreeSet::new(), &prev, &reviewed).unwrap_err();
        assert!(err.to_string().contains("has no Agent-Bus-Agent trailer"), "{err}");
    }

    #[test]
    fn verify_authorship_rejects_reviewer_authored_commit() {
        let (prev, reviewed) = (hash(1), hash(2));
        let c = hash(3);
        let mut trailers = std::collections::BTreeMap::new();
        trailers.insert(c.as_str(), vec!["bob"]);
        let _guard = mock_authorship(&prev, &reviewed, &[&c], trailers);
        let bob = a("bob");
        let mut expected = BTreeSet::new();
        expected.insert(bob.clone());
        let err = verify_authorship(&PathBuf::from("."), &bob, &expected, &prev, &reviewed).unwrap_err();
        assert!(err.to_string().contains("ineligible to merge"), "{err}");
    }

    #[test]
    fn verify_authorship_rejects_author_mismatch() {
        let (prev, reviewed) = (hash(1), hash(2));
        let c = hash(3);
        let mut trailers = std::collections::BTreeMap::new();
        trailers.insert(c.as_str(), vec!["carol"]);
        let _guard = mock_authorship(&prev, &reviewed, &[&c], trailers);
        let bob = a("bob");
        let mut expected = BTreeSet::new();
        expected.insert(a("alice"));
        let err = verify_authorship(&PathBuf::from("."), &bob, &expected, &prev, &reviewed).unwrap_err();
        assert!(err.to_string().contains("do not match nomination authors"), "{err}");
    }

    #[test]
    fn verify_authorship_succeeds_and_returns_introduced_commits() {
        let (prev, reviewed) = (hash(1), hash(2));
        let (c1, c2) = (hash(3), hash(4));
        let mut trailers = std::collections::BTreeMap::new();
        trailers.insert(c1.as_str(), vec!["alice"]);
        trailers.insert(c2.as_str(), vec!["alice"]);
        let _guard = mock_authorship(&prev, &reviewed, &[&c1, &c2], trailers);
        let bob = a("bob");
        let mut expected = BTreeSet::new();
        expected.insert(a("alice"));
        let introduced = verify_authorship(&PathBuf::from("."), &bob, &expected, &prev, &reviewed).unwrap();
        assert_eq!(introduced, vec![c1, c2]);
    }

    #[test]
    fn reconstruct_candidate_rejects_multiple_merge_bases() {
        let (prev, reviewed) = (hash(1), hash(2));
        let bob = a("bob");
        let _guard = MockGit::new()
            .on(&["merge-base", "--all", &prev, &reviewed], GitOutput::ok(format!("{}\n{}", hash(5), hash(6))))
            .install();
        let err = reconstruct_candidate(&PathBuf::from("."), &prev, &reviewed, &bob).unwrap_err();
        assert!(err.to_string().contains("do not have exactly one merge base"), "{err}");
    }

    #[test]
    fn path_in_claim_prefix_and_exact() {
        let glob = crate::scalars::PathClaim::parse("src/**".to_string()).unwrap();
        assert!(path_in_claim("src/lib.rs", &glob));
        assert!(path_in_claim("src", &glob));
        assert!(!path_in_claim("other/lib.rs", &glob));
        let exact = crate::scalars::PathClaim::parse("README.md".to_string()).unwrap();
        assert!(path_in_claim("README.md", &exact));
        assert!(!path_in_claim("README.md.bak", &exact));
    }

    // --------------------------------------------------------- real-repo
    // `authorize`/`merge_ready`/`merged`/`reconcile`/`audit_main` all call
    // `ctx.load_state()`, which walks real git history through a couple of
    // call sites that bypass the `MockGit` seam (`history::blob_bytes`,
    // `BusCtx::bus_json`) — so these are exercised against a small real
    // throwaway repository instead, calling the Rust functions directly
    // (not the CLI binary) so individual error branches can be triggered
    // precisely.

    struct Fixture {
        _dir: tempfile::TempDir,
        path: std::path::PathBuf,
        ctx: BusCtx,
        #[allow(dead_code)]
        alice: Agent,
        bob: Agent,
        nomination: EventId,
        feature: String,
        previous_main: String,
        merge_engine_epoch: String,
    }

    /// Bootstraps a repo, registers alice (implementor) and bob (reviewer),
    /// commits `feature.txt` plus `extra_files` (each with an
    /// `Agent-Bus-Agent: alice` trailer, or `trailer_agent` if given) on top
    /// of `main`, and nominates+takes it with `review_scope`.
    fn build_fixture(review_scope: &[&str], extra_files: &[&str], trailer_agent: &str) -> Fixture {
        let dir = init_repo();
        let path = dir.path().to_path_buf();
        let ctx = bootstrap(&path, &["coord1"]);
        let alice = register(&ctx, "alice", Role::Implementor);
        let bob = register(&ctx, "bob", Role::Reviewer);
        let previous_main = git(&path, &["rev-parse", "main"]);

        git(&path, &["checkout", "--quiet", "--detach", &previous_main]);
        std::fs::write(path.join("feature.txt"), "feature content\n").unwrap();
        for f in extra_files {
            std::fs::write(path.join(f), "extra\n").unwrap();
        }
        git(&path, &["add", "."]);
        git(&path, &["commit", "-q", "-m", &format!("add feature\n\nAgent-Bus-Agent: {trailer_agent}")]);
        let feature = git(&path, &["rev-parse", "HEAD"]);
        git(&path, &["checkout", "--quiet", "main"]);

        let nomination =
            nominate_review(&ctx, &alice, &bob, "refs/heads/agent/alice/feature", review_scope, &["build"]);
        take_review(&ctx, &bob, &nomination);
        let merge_engine_epoch = ctx.load_state().unwrap().current_merge_engine_epoch.to_string();
        Fixture { _dir: dir, path, ctx, alice, bob, nomination, feature, previous_main, merge_engine_epoch }
    }

    fn fixture() -> Fixture {
        build_fixture(&["feature.txt"], &[], "alice")
    }

    fn auth_json(f: &Fixture, candidate: &str, review_scope: &[&str]) -> serde_json::Value {
        serde_json::json!({
            "nomination": f.nomination.as_str(),
            "product_branch": "refs/heads/agent/alice/feature",
            "previous_main": f.previous_main,
            "reviewed_commit": f.feature,
            "candidate": candidate,
            "merge_engine_epoch": f.merge_engine_epoch,
            "checks": [{"command": "build", "result": "passed"}],
            "finding_dispositions": [],
            "evidence": [],
            "reviewed_scope": review_scope,
            "limitations": [],
            "summary": "looks good",
        })
    }

    fn write_auth(f: &Fixture, name: &str, candidate: &str, review_scope: &[&str]) -> String {
        write_json(&f.path, name, &auth_json(f, candidate, review_scope))
    }

    // ------------------------------------------------- simple CLI wrappers
    // `decline`/`withdraw`/`changes`/`clear`/`supersede`/`reassign` are thin
    // wrappers around `bus::publish_event`; `tests/cli_flow.rs` never
    // exercises them (it only nominates, takes, authorizes, and merges), so
    // they get a direct success-path test each here.

    #[test]
    fn decline_publishes_review_nomination_declined() {
        let f = fixture();
        decline(&f.ctx, "bob", f.nomination.as_str(), "not the right reviewer").expect("decline succeeds");
    }

    #[test]
    fn withdraw_publishes_review_withdrawn() {
        let f = fixture();
        withdraw(&f.ctx, "alice", f.nomination.as_str(), "pausing this work").expect("withdraw succeeds");
    }

    fn changes_json(f: &Fixture) -> serde_json::Value {
        serde_json::json!({
            "nomination": f.nomination.as_str(),
            "reviewed_commit": f.feature,
            "findings": [{
                "id": "f1", "priority": "normal", "locations": [],
                "rationale": "needs work", "closure_conditions": "fix it",
            }],
            "evidence": [],
        })
    }

    #[test]
    fn changes_publishes_review_changes_requested() {
        let f = fixture();
        let file = write_json(&f.path, "changes.json", &changes_json(&f));
        changes(&f.ctx, "bob", &file).expect("changes succeeds");
    }

    #[test]
    fn clear_publishes_review_findings_cleared() {
        let f = fixture();
        let file = write_json(&f.path, "changes.json", &changes_json(&f));
        changes(&f.ctx, "bob", &file).unwrap();
        let changes_event = EventId::new(&f.bob, 2); // bob:0 register, bob:1 take, bob:2 changes
        let clear_file = write_json(
            &f.path,
            "clear.json",
            &serde_json::json!({
                "nomination": f.nomination.as_str(),
                "changes_event": changes_event.as_str(),
                "finding_id": "f1",
                "resolved_commit": f.feature,
                "summary": "fixed it",
            }),
        );
        clear(&f.ctx, "bob", &clear_file).expect("clear succeeds");
    }

    #[test]
    fn supersede_publishes_review_findings_superseded() {
        let f = fixture();
        let file = write_json(&f.path, "changes.json", &changes_json(&f));
        changes(&f.ctx, "bob", &file).unwrap();
        let changes_event = EventId::new(&f.bob, 2);
        let supersede_file = write_json(
            &f.path,
            "supersede.json",
            &serde_json::json!({
                "nomination": f.nomination.as_str(),
                "changes_event": changes_event.as_str(),
                "finding_id": "f1",
                "rationale": "no longer applies",
            }),
        );
        supersede(&f.ctx, "bob", &supersede_file).expect("supersede succeeds");
    }

    #[test]
    fn reassign_publishes_review_reassigned_to_a_new_reviewer() {
        let f = fixture();
        register(&f.ctx, "carol", Role::Reviewer);
        let file = write_json(
            &f.path,
            "reassign.json",
            &serde_json::json!({
                "authors": ["alice"],
                "product_branch": "refs/heads/agent/alice/feature",
                "reviewer": "carol",
                "required_checks": ["build"],
                "review_scope": ["feature.txt"],
                "summary": "add feature",
                "target_branch": "refs/heads/main",
                "evidence": [],
                "replaces": f.nomination.as_str(),
                "reason": "bob is away",
            }),
        );
        reassign(&f.ctx, "alice", &file).expect("reassign succeeds");
    }

    #[test]
    fn authorize_rejects_unknown_nomination() {
        let f = fixture();
        let bogus = EventId::parse("alice:99".to_string()).unwrap();
        let file = write_json(
            &f.path,
            "auth.json",
            &serde_json::json!({
                "nomination": bogus.as_str(),
                "product_branch": "refs/heads/agent/alice/feature",
                "previous_main": f.previous_main,
                "reviewed_commit": f.feature,
                "candidate": hash(1),
                "merge_engine_epoch": f.merge_engine_epoch,
                "checks": [{"command": "build", "result": "passed"}],
                "finding_dispositions": [],
                "evidence": [],
                "reviewed_scope": ["feature.txt"],
                "limitations": [],
                "summary": "looks good",
            }),
        );
        let err = authorize(&f.ctx, "bob", &file).unwrap_err();
        assert!(err.to_string().contains("unknown nomination"), "{err}");
    }

    #[test]
    fn authorize_rejects_when_reviewer_authored_a_commit() {
        let f = build_fixture(&["feature.txt"], &[], "bob");
        let file = write_auth(&f, "auth.json", &hash(1), &["feature.txt"]);
        let err = authorize(&f.ctx, "bob", &file).unwrap_err();
        assert!(err.to_string().contains("ineligible to merge"), "{err}");
    }

    #[test]
    fn authorize_rejects_reconstruction_mismatch() {
        let f = fixture();
        let wrong_candidate = hash(999);
        let file = write_auth(&f, "auth.json", &wrong_candidate, &["feature.txt"]);
        let err = authorize(&f.ctx, "bob", &file).unwrap_err();
        assert!(err.to_string().contains("does not match the deterministic reconstruction"), "{err}");
    }

    #[test]
    fn authorize_rejects_missing_candidate_tag() {
        let f = fixture();
        let real_candidate =
            reconstruct_candidate(&f.path, &f.previous_main, &f.feature, &f.bob).expect("reconstruction succeeds");
        let file = write_auth(&f, "auth.json", &real_candidate, &["feature.txt"]);
        let err = authorize(&f.ctx, "bob", &file).unwrap_err();
        assert!(err.to_string().contains("candidate tag is not fetchable"), "{err}");
    }

    /// g-reviewer:4: `prepare-merge` must fail outright when the candidate
    /// tag cannot actually reach `origin` -- a local-only tag is useless to
    /// every other agent and to `--linked` validation elsewhere. Simulated
    /// via a deliberately unreachable "origin" (a nonexistent local path);
    /// any real transport failure surfaces the same way.
    #[test]
    fn prepare_merge_fails_when_candidate_tag_push_to_origin_fails() {
        let f = fixture();
        git(&f.path, &["remote", "add", "origin", "/nonexistent/not-a-repo"]);
        let ctx = BusCtx { repo_root: f.path.clone(), has_origin: true };
        let err = prepare_merge(&ctx, "bob", f.nomination.as_str(), &f.feature).unwrap_err();
        assert!(err.to_string().contains("failed to publish candidate tag"), "{err}");
        assert!(err.to_string().contains("to origin"), "{err}");
    }

    /// g-reviewer:4: a candidate tag that exists only in the reviewer's own
    /// clone (never pushed, or later deleted from origin) must not pass
    /// `authorize` -- `tag_exists_at` alone can't tell the two apart from a
    /// tag that genuinely reached origin.
    #[test]
    fn authorize_rejects_candidate_tag_that_never_reached_origin() {
        let f = fixture();
        let origin = init_repo();
        git(&f.path, &["remote", "add", "origin", &origin.path().to_string_lossy()]);
        let ctx = BusCtx { repo_root: f.path.clone(), has_origin: true };

        let real_candidate =
            reconstruct_candidate(&f.path, &f.previous_main, &f.feature, &f.bob).expect("reconstruction succeeds");
        // Tag it locally (so tag_exists_at alone would pass) but deliberately
        // never push it to `origin`.
        git(&f.path, &["tag", &format!("agent-candidate/bob/{real_candidate}"), &real_candidate]);
        let file = write_auth(&f, "auth.json", &real_candidate, &["feature.txt"]);
        let err = authorize(&ctx, "bob", &file).unwrap_err();
        assert!(err.to_string().contains("not fetchable from origin"), "{err}");
    }

    /// Real, correct `prepare-merge` + `authorize`, so later tests can build
    /// on a genuinely authorized nomination without repeating the setup.
    fn authorize_fixture(f: &Fixture) -> (String, EventId) {
        let candidate =
            reconstruct_candidate(&f.path, &f.previous_main, &f.feature, &f.bob).expect("reconstruction succeeds");
        git(&f.path, &["tag", &format!("agent-candidate/bob/{candidate}"), &candidate]);
        let file = write_auth(f, "auth.json", &candidate, &["feature.txt"]);
        authorize(&f.ctx, "bob", &file).expect("authorize succeeds");
        let authorization_id = EventId::new(&f.bob, 2); // bob:0 register, bob:1 take, bob:2 authorize
        (candidate, authorization_id)
    }

    #[test]
    fn merge_ready_rejects_unknown_authorization() {
        let f = fixture();
        let bogus = EventId::parse("bob:99".to_string()).unwrap();
        let err = merge_ready(&f.ctx, "bob", bogus.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("unknown authorization"), "{err}");
    }

    #[test]
    fn merge_ready_rejects_wrong_authorizer() {
        let f = fixture();
        let (_candidate, authorization_id) = authorize_fixture(&f);
        let carol = register(&f.ctx, "carol", Role::Reviewer);
        let _ = carol;
        let err = merge_ready(&f.ctx, "carol", authorization_id.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("was not published by the given reviewer"), "{err}");
    }

    #[test]
    fn merge_ready_rejects_main_advanced() {
        let f = fixture();
        let (_candidate, authorization_id) = authorize_fixture(&f);
        // Advance `main` past the authorized `previous_main` out from under it.
        git(&f.path, &["update-ref", "refs/heads/main", &f.feature]);
        let err = merge_ready(&f.ctx, "bob", authorization_id.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("has advanced past authorized previous_main"), "{err}");
    }

    #[test]
    fn merge_ready_rejects_open_finding_surfacing_after_authorization() {
        let f = fixture();
        let (_candidate, authorization_id) = authorize_fixture(&f);
        // A finding filed *after* authorization (the code does not forbid
        // this) must still block `merge-ready` from using the now-stale
        // authorization.
        let changes = ReviewChangesRequested {
            nomination: f.nomination.clone(),
            reviewed_commit: ObjectId::parse(f.feature.clone()).unwrap(),
            findings: vec![crate::common::Finding {
                id: crate::scalars::Short::parse("f1".into()).unwrap(),
                priority: crate::common::Priority::Normal,
                locations: vec![],
                rationale: Text::parse("late finding".into()).unwrap(),
                closure_conditions: Text::parse("fix it".into()).unwrap(),
            }],
            evidence: StringSet::default(),
        };
        bus::publish_event(&f.ctx, &f.bob, EventData::ReviewChangesRequested(changes), vec![f.nomination.clone()])
            .unwrap();
        let err = merge_ready(&f.ctx, "bob", authorization_id.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("has no terminal disposition"), "{err}");
    }

    #[test]
    fn merge_ready_rejects_changed_path_outside_reviewed_scope() {
        // The reviewed commit touches sneaky.txt too, but review_scope only
        // ever names feature.txt — merge-ready's own diff check is what
        // catches this (authorize/apply never inspect changed paths).
        let f = build_fixture(&["feature.txt"], &["sneaky.txt"], "alice");
        let (_candidate, authorization_id) = authorize_fixture(&f);
        let err = merge_ready(&f.ctx, "bob", authorization_id.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("is outside reviewed_scope"), "{err}");
    }

    /// Publishes a hand-built `review.merge_authorized` directly (bypassing
    /// `review_cmds::authorize`'s own reconstruction/tag gate entirely, the
    /// way a direct push onto the bus branch would), so `merge_ready`'s
    /// independent real-git checks on the *content* of `candidate` can be
    /// exercised on their own.
    fn publish_raw_authorization(f: &Fixture, candidate: &str) -> EventId {
        let data = ReviewMergeAuthorized {
            nomination: f.nomination.clone(),
            product_branch: crate::scalars::Branch::parse("refs/heads/agent/alice/feature".to_string()).unwrap(),
            previous_main: ObjectId::parse(f.previous_main.clone()).unwrap(),
            reviewed_commit: ObjectId::parse(f.feature.clone()).unwrap(),
            candidate: ObjectId::parse(candidate.to_string()).unwrap(),
            merge_engine_epoch: EventId::parse(f.merge_engine_epoch.clone()).unwrap(),
            checks: vec![crate::common::CheckResult {
                command: Text::parse("build".into()).unwrap(),
                result: crate::common::CheckOutcome::Passed,
                evidence: None,
            }],
            finding_dispositions: vec![],
            evidence: StringSet::default(),
            reviewed_scope: StringSet::from_iter(vec![crate::scalars::PathClaim::parse("feature.txt".into()).unwrap()]),
            limitations: vec![],
            summary: Text::parse("looks good".into()).unwrap(),
        };
        let mut refs = vec![data.nomination.clone(), data.merge_engine_epoch.clone()];
        refs.extend(data.evidence.iter().cloned());
        bus::publish_event(&f.ctx, &f.bob, EventData::ReviewMergeAuthorized(data), refs).unwrap().id
    }

    #[test]
    fn merge_ready_rejects_hand_pushed_candidate_with_wrong_parents() {
        let f = fixture();
        let tree = git(&f.path, &["rev-parse", &format!("{}^{{tree}}", f.feature)]);
        // Single-parent "candidate": parents = [feature], not
        // [previous_main, feature].
        let bad = git(&f.path, &["commit-tree", &tree, "-p", &f.feature, "-m", "bad\n\nAgent-Bus-Reviewer: bob"]);
        let authorization_id = publish_raw_authorization(&f, &bad);
        let err = merge_ready(&f.ctx, "bob", authorization_id.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("candidate parents do not match"), "{err}");
    }

    #[test]
    fn merge_ready_rejects_hand_pushed_candidate_missing_trailer() {
        let f = fixture();
        let tree = git(&f.path, &["rev-parse", &format!("{}^{{tree}}", f.feature)]);
        let bad = git(&f.path, &["commit-tree", &tree, "-p", &f.previous_main, "-p", &f.feature, "-m", "no trailer"]);
        let authorization_id = publish_raw_authorization(&f, &bad);
        let err = merge_ready(&f.ctx, "bob", authorization_id.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("exactly one matching Agent-Bus-Reviewer trailer"), "{err}");
    }

    #[test]
    fn merge_ready_rejects_hand_pushed_candidate_with_wrong_reviewer_trailer_name() {
        // Right parents, exactly one Agent-Bus-Reviewer trailer -- but it
        // names a different agent than the reviewer running `merge-ready`.
        // The `reviewer_trailers.len() != 1` branch is already covered by
        // `merge_ready_rejects_hand_pushed_candidate_missing_trailer` (zero
        // trailers); this exercises the other half of that check's `||`
        // (exactly one trailer, wrong identity), which nothing else here
        // constructs a plausible-enough forged candidate to reach.
        let f = fixture();
        let tree = git(&f.path, &["rev-parse", &format!("{}^{{tree}}", f.feature)]);
        let bad = git(
            &f.path,
            &["commit-tree", &tree, "-p", &f.previous_main, "-p", &f.feature, "-m", "bad\n\nAgent-Bus-Reviewer: carol"],
        );
        let authorization_id = publish_raw_authorization(&f, &bad);
        let err = merge_ready(&f.ctx, "bob", authorization_id.as_str(), false).unwrap_err();
        assert!(err.to_string().contains("exactly one matching Agent-Bus-Reviewer trailer"), "{err}");
    }

    #[test]
    fn merged_rejects_previous_main_mismatch() {
        let f = fixture();
        let (candidate, authorization_id) = authorize_fixture(&f);
        git(&f.path, &["update-ref", "refs/heads/main", &candidate]);
        let file = write_json(
            &f.path,
            "merged.json",
            &serde_json::json!({
                "authorization": authorization_id.as_str(),
                "previous_main": f.feature, // wrong: should be f.previous_main
                "main_commit": candidate,
                "product_branch": "refs/heads/agent/alice/feature",
                "reviewed_commit": f.feature,
                "summary": "merged",
            }),
        );
        let err = merged(&f.ctx, "bob", &file).unwrap_err();
        assert!(err.to_string().contains("first parent does not match previous_main"), "{err}");
    }

    #[test]
    fn merged_rejects_when_main_not_advanced() {
        let f = fixture();
        let (candidate, authorization_id) = authorize_fixture(&f);
        // main is deliberately left pointing at previous_main.
        let file = write_json(
            &f.path,
            "merged.json",
            &serde_json::json!({
                "authorization": authorization_id.as_str(),
                "previous_main": f.previous_main,
                "main_commit": candidate,
                "product_branch": "refs/heads/agent/alice/feature",
                "reviewed_commit": f.feature,
                "summary": "merged",
            }),
        );
        let err = merged(&f.ctx, "bob", &file).unwrap_err();
        assert!(err.to_string().contains("does not currently equal main_commit"), "{err}");
    }

    fn reconcile_json(f: &Fixture, authorization_id: &EventId, candidate: &str) -> serde_json::Value {
        serde_json::json!({
            "authorization": authorization_id.as_str(),
            "previous_main": f.previous_main,
            "main_commit": candidate,
            "product_branch": "refs/heads/agent/alice/feature",
            "reviewed_commit": f.feature,
            "reason": "manual merge outside the bus",
            "user_authority": "repo owner",
        })
    }

    #[test]
    fn reconcile_rejects_non_first_parent_successor() {
        let f = fixture();
        let (candidate, authorization_id) = authorize_fixture(&f);
        // main is never advanced to `candidate`.
        let file = write_json(&f.path, "reconcile.json", &reconcile_json(&f, &authorization_id, &candidate));
        let err = reconcile(&f.ctx, "coord1", &file).unwrap_err();
        assert!(err.to_string().contains("not a first-parent successor"), "{err}");
    }

    #[test]
    fn reconcile_succeeds_when_main_was_advanced_out_of_band() {
        let f = fixture();
        let (candidate, authorization_id) = authorize_fixture(&f);
        git(&f.path, &["update-ref", "refs/heads/main", &candidate]);
        let file = write_json(&f.path, "reconcile.json", &reconcile_json(&f, &authorization_id, &candidate));
        reconcile(&f.ctx, "coord1", &file).expect("reconcile succeeds");
    }

    fn merge_commit(path: &std::path::Path, first_parent: &str, second_parent: &str, message: &str) -> String {
        let tree = git(path, &["rev-parse", &format!("{second_parent}^{{tree}}")]);
        git(path, &["commit-tree", &tree, "-p", first_parent, "-p", second_parent, "-m", message])
    }

    fn problems(findings: &[Value]) -> Vec<String> {
        findings.iter().map(|v| v["problem"].as_str().unwrap().to_string()).collect()
    }

    #[test]
    fn audit_main_flags_non_merge_commit() {
        let f = fixture();
        let root = git(&f.path, &["rev-parse", &f.previous_main]);
        let stray = author_commit(&f.path, &root, "stray.txt", "x\n", "alice");
        let findings = audit_main_findings(&f.ctx, Some(&stray)).unwrap();
        let problems = problems(&findings);
        assert!(problems.iter().any(|p| p.contains("not a two-parent merge")), "{problems:?}");
    }

    #[test]
    fn audit_main_flags_missing_reviewer_trailer() {
        let f = fixture();
        let root = git(&f.path, &["rev-parse", &f.previous_main]);
        let second = author_commit(&f.path, &root, "x.txt", "x\n", "alice");
        let merge = merge_commit(&f.path, &root, &second, "merge without trailer");
        let findings = audit_main_findings(&f.ctx, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems.iter().any(|p| p.contains("missing or duplicate Agent-Bus-Reviewer trailer")),
            "{problems:?}"
        );
    }

    #[test]
    fn audit_main_flags_non_reviewer_identity() {
        let f = fixture();
        let root = git(&f.path, &["rev-parse", &f.previous_main]);
        let second = author_commit(&f.path, &root, "x.txt", "x\n", "alice");
        // alice is a registered implementor, not a reviewer.
        let merge = merge_commit(&f.path, &root, &second, "merge\n\nAgent-Bus-Reviewer: alice");
        let findings = audit_main_findings(&f.ctx, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(problems.iter().any(|p| p.contains("non-reviewer identity")), "{problems:?}");
    }

    #[test]
    fn audit_main_flags_missing_author_trailer() {
        let f = fixture();
        let root = git(&f.path, &["rev-parse", &f.previous_main]);
        git(&f.path, &["checkout", "--quiet", "--detach", &root]);
        std::fs::write(f.path.join("untrailered.txt"), "x\n").unwrap();
        git(&f.path, &["add", "untrailered.txt"]);
        git(&f.path, &["commit", "-q", "-m", "no trailer at all"]);
        let second = git(&f.path, &["rev-parse", "HEAD"]);
        let merge = merge_commit(&f.path, &root, &second, "merge\n\nAgent-Bus-Reviewer: bob");
        let findings = audit_main_findings(&f.ctx, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(problems.iter().any(|p| p.contains("author trailer check failed")), "{problems:?}");
    }

    #[test]
    fn audit_main_flags_reviewer_authored_introduced_commit() {
        let f = fixture();
        let root = git(&f.path, &["rev-parse", &f.previous_main]);
        // The introduced commit is trailered to bob, who is also the named
        // Agent-Bus-Reviewer on the merge itself.
        let second = author_commit(&f.path, &root, "x.txt", "x\n", "bob");
        let merge = merge_commit(&f.path, &root, &second, "merge\n\nAgent-Bus-Reviewer: bob");
        let findings = audit_main_findings(&f.ctx, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(problems.iter().any(|p| p.contains("reviewer authored an introduced commit")), "{problems:?}");
    }

    #[test]
    fn audit_main_flags_no_matching_authorization() {
        let f = fixture();
        let root = git(&f.path, &["rev-parse", &f.previous_main]);
        // Structurally plausible (right trailer, right roles, right
        // authorship) but no review.merge_authorized event names it.
        let merge = merge_commit(&f.path, &root, &f.feature, "merge\n\nAgent-Bus-Reviewer: bob");
        let findings = audit_main_findings(&f.ctx, Some(&merge)).unwrap();
        let problems = problems(&findings);
        assert!(problems.iter().any(|p| p.contains("no review.merge_authorized matches")), "{problems:?}");
    }

    #[test]
    fn audit_main_flags_authorized_nomination_but_wrong_exact_commit() {
        // AGENT_BUS_SCHEMA.md section 9 requires the correlation to match the
        // *exact* candidate/previous_main/reviewed_commit of a real
        // review.merge_authorized event, not merely "some authorization
        // exists for a nomination with the same authors/reviewer". Build a
        // genuinely authorized nomination (real candidate `candidate`), then
        // present a *different* hand-built merge commit on the same
        // previous_main/reviewed_commit pair, with the same authors and the
        // same Agent-Bus-Reviewer identity (bob) -- everything a name-only
        // correlation would accept -- but not the commit the authorization
        // actually names. If `audit_main_findings` ever weakened its match to
        // authors+reviewer only (dropping the candidate/previous_main/
        // reviewed_commit equality checks), this near-miss would wrongly
        // correlate against the real authorization and this test would fail
        // to see any finding.
        let f = fixture();
        let (candidate, _authorization_id) = authorize_fixture(&f);
        let near_miss =
            merge_commit(&f.path, &f.previous_main, &f.feature, "a different merge message\n\nAgent-Bus-Reviewer: bob");
        assert_ne!(near_miss, candidate, "the hand-built merge must not coincide with the real candidate");
        let findings = audit_main_findings(&f.ctx, Some(&near_miss)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems.iter().any(|p| p.contains("no review.merge_authorized matches this exact candidate/previous_main/reviewed_commit")),
            "{problems:?}"
        );
    }

    #[test]
    fn audit_main_flags_missing_receipt() {
        let f = fixture();
        let (candidate, _authorization_id) = authorize_fixture(&f);
        // Authorized for real, but neither `merged` nor `reconcile` was ever
        // published — `refs/heads/main` is advanced out of band instead, the
        // way a hand-pushed merge would.
        git(&f.path, &["update-ref", "refs/heads/main", &candidate]);
        let findings = audit_main_findings(&f.ctx, Some(&candidate)).unwrap();
        let problems = problems(&findings);
        assert!(
            problems.iter().any(|p| p.contains("missing review.merged/review.merge_reconciled receipt")),
            "{problems:?}"
        );
    }

    #[test]
    fn audit_main_clean_when_fully_correlated() {
        let f = fixture();
        let (candidate, authorization_id) = authorize_fixture(&f);
        git(&f.path, &["update-ref", "refs/heads/main", &candidate]);
        let file = write_json(&f.path, "merged.json", &{
            serde_json::json!({
                "authorization": authorization_id.as_str(),
                "previous_main": f.previous_main,
                "main_commit": candidate,
                "product_branch": "refs/heads/agent/alice/feature",
                "reviewed_commit": f.feature,
                "summary": "merged",
            })
        });
        merged(&f.ctx, "bob", &file).expect("merged succeeds");
        let findings = audit_main_findings(&f.ctx, Some(&candidate)).unwrap();
        assert!(findings.is_empty(), "{findings:?}");
    }
}
