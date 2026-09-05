//! Git-linked cross-checks for the review/merge protocol's `candidate`
//! (AGENT_REVIEW.md section 7) that `apply.rs` deliberately leaves out of
//! its pure, git-repo-free reduction -- see `apply.rs`'s own module doc:
//! "Git/product-repo cross-checks (candidate tags, merge-authorship
//! trailers, `main` history) are deliberately NOT done here."
//!
//! Ported near-verbatim from the shipped version-one helper's
//! `review_cmds.rs` (`verify_authorship`/`reconstruct_candidate`), which
//! solved exactly this problem with an extensively tested design (~30
//! tests there). Only the agent/collection types differ: v2 stores a
//! nomination's authors as `StringSet<Agent>`
//! (`state::ReviewChain::current_request.authors`), not v1's plain
//! `BTreeSet<Agent>`, so callers convert at the boundary.
//!
//! Two call sites use these:
//! - `cli::prepare_merge`, the reviewer-run convenience step
//!   (AGENT_REVIEW.md section 7 step 4) that constructs and publishes the
//!   candidate tag; and
//! - `coordinator::drain_outbox`'s gate for `review.merge_authorized`
//!   candidates, which re-runs everything here again at the actual
//!   publication boundary -- nothing stops a hand-crafted `submit --kind
//!   review.merge_authorized` from skipping `prepare-merge` entirely, so
//!   trusting its own claims would leave this gap wide open regardless of
//!   what `prepare-merge` itself checks.

use crate::error::{invalid, AbResult};
use crate::scalars::Agent;
use std::collections::BTreeSet;
use std::path::Path;

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

/// AGENT_REVIEW.md sections 3/7: every commit introduced by `reviewed_commit`
/// over `previous_main` must carry an `Agent-Bus-Agent` trailer, the union of
/// those trailers must be exactly the nomination's `authors`, and `reviewer`
/// must not be among them. Returns the introduced commits (in
/// `previous_main` order) for callers that also need them.
pub(crate) fn verify_authorship(
    repo: &Path,
    reviewer: &Agent,
    expected_authors: &BTreeSet<Agent>,
    previous_main: &str,
    reviewed_commit: &str,
) -> AbResult<Vec<String>> {
    let introduced = crate::gitrepo::commits_between_first_parent_exclusive(
        repo,
        previous_main,
        reviewed_commit,
    )?;
    if introduced.is_empty() {
        return Err(invalid(
            "reviewed_commit introduces no content over previous_main",
        ));
    }
    let mut authors = BTreeSet::new();
    for c in &introduced {
        let a = commit_authors(repo, c)?;
        if a.is_empty() {
            return Err(invalid(format!(
                "commit {c} has no Agent-Bus-Agent trailer"
            )));
        }
        if a.contains(reviewer) {
            return Err(invalid(format!(
                "reviewer {reviewer} authored commit {c}; ineligible to merge"
            )));
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

/// Deterministically reconstructs the exact candidate object id
/// `cli::prepare_merge` would produce for `(previous_main, reviewed_commit,
/// reviewer)` (AGENT_REVIEW.md section 7). Used both to construct a
/// candidate there, and in `coordinator`'s gate to verify one a
/// `review.merge_authorized` payload merely claims, without trusting
/// anything it asserts.
pub(crate) fn reconstruct_candidate(
    repo: &Path,
    previous_main: &str,
    reviewed_commit: &str,
    reviewer: &Agent,
) -> AbResult<String> {
    if crate::gitrepo::merge_base_count(repo, previous_main, reviewed_commit)? != 1 {
        return Err(invalid(
            "previous_main and reviewed_commit do not have exactly one merge base",
        ));
    }
    let tree = crate::gitrepo::merge_tree_write_tree(repo, previous_main, reviewed_commit)?;
    let message = format!("agent-bus candidate\n\nAgent-Bus-Reviewer: {reviewer}\n");
    crate::gitrepo::commit_tree_deterministic(
        repo,
        &tree,
        &[previous_main, reviewed_commit],
        &message,
    )
}

/// `refs/tags/agent-candidate/<reviewer>/<candidate>` (AGENT_REVIEW.md
/// sections 7/9): the immutable candidate tag naming.
pub(crate) fn candidate_tag_name(reviewer: &Agent, candidate: &str) -> String {
    format!("agent-candidate/{reviewer}/{candidate}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gitrepo::mock::{MockGit, MockGuard};
    use crate::gitrepo::GitOutput;
    use std::path::PathBuf;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn hash(n: u64) -> String {
        format!("{n:040x}")
    }

    /// Installs a `MockGit` that answers `rev-list <previous_main>..
    /// <reviewed_commit>` with `commits`, and `show -s --format=%B <c>` /
    /// `interpret-trailers --parse` for each with the `Agent-Bus-Agent`
    /// trailers named in `trailer_agents` (mirrors v1's own
    /// `mock_authorship` test helper).
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
            .map(|(k, v)| {
                (
                    k.to_string(),
                    v.into_iter().map(|s| s.to_string()).collect(),
                )
            })
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
                            agents
                                .iter()
                                .map(|ag| format!("Agent-Bus-Agent: {ag}"))
                                .collect::<Vec<_>>()
                                .join("\n")
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
        let err = verify_authorship(
            &PathBuf::from("."),
            &bob,
            &BTreeSet::new(),
            &prev,
            &reviewed,
        )
        .unwrap_err();
        assert!(err.to_string().contains("introduces no content"), "{err}");
    }

    #[test]
    fn verify_authorship_rejects_missing_author_trailer() {
        let (prev, reviewed) = (hash(1), hash(2));
        let c = hash(3);
        let _guard = mock_authorship(&prev, &reviewed, &[&c], Default::default());
        let bob = a("bob");
        let err = verify_authorship(
            &PathBuf::from("."),
            &bob,
            &BTreeSet::new(),
            &prev,
            &reviewed,
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("has no Agent-Bus-Agent trailer"),
            "{err}"
        );
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
        let err =
            verify_authorship(&PathBuf::from("."), &bob, &expected, &prev, &reviewed).unwrap_err();
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
        let err =
            verify_authorship(&PathBuf::from("."), &bob, &expected, &prev, &reviewed).unwrap_err();
        assert!(
            err.to_string().contains("do not match nomination authors"),
            "{err}"
        );
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
        let introduced =
            verify_authorship(&PathBuf::from("."), &bob, &expected, &prev, &reviewed).unwrap();
        assert_eq!(introduced, vec![c1, c2]);
    }

    #[test]
    fn verify_authorship_accepts_multiple_authors_across_commits() {
        let (prev, reviewed) = (hash(1), hash(2));
        let (c1, c2) = (hash(3), hash(4));
        let mut trailers = std::collections::BTreeMap::new();
        trailers.insert(c1.as_str(), vec!["alice"]);
        trailers.insert(c2.as_str(), vec!["carol"]);
        let _guard = mock_authorship(&prev, &reviewed, &[&c1, &c2], trailers);
        let bob = a("bob");
        let expected: BTreeSet<Agent> = [a("alice"), a("carol")].into_iter().collect();
        let introduced =
            verify_authorship(&PathBuf::from("."), &bob, &expected, &prev, &reviewed).unwrap();
        assert_eq!(introduced, vec![c1, c2]);
    }

    #[test]
    fn reconstruct_candidate_rejects_multiple_merge_bases() {
        let (prev, reviewed) = (hash(1), hash(2));
        let bob = a("bob");
        let _guard = MockGit::new()
            .on(
                &["merge-base", "--all", &prev, &reviewed],
                GitOutput::ok(format!("{}\n{}", hash(5), hash(6))),
            )
            .install();
        let err = reconstruct_candidate(&PathBuf::from("."), &prev, &reviewed, &bob).unwrap_err();
        assert!(
            err.to_string()
                .contains("do not have exactly one merge base"),
            "{err}"
        );
    }

    #[test]
    fn reconstruct_candidate_rejects_zero_merge_bases() {
        let (prev, reviewed) = (hash(1), hash(2));
        let bob = a("bob");
        let _guard = MockGit::new()
            .on(
                &["merge-base", "--all", &prev, &reviewed],
                GitOutput::ok(""),
            )
            .install();
        let err = reconstruct_candidate(&PathBuf::from("."), &prev, &reviewed, &bob).unwrap_err();
        assert!(
            err.to_string()
                .contains("do not have exactly one merge base"),
            "{err}"
        );
    }

    #[test]
    fn candidate_tag_name_matches_the_documented_format() {
        let bob = a("bob");
        assert_eq!(
            candidate_tag_name(&bob, &hash(7)),
            format!("agent-candidate/bob/{}", hash(7))
        );
    }
}
