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

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn hash(n: u64) -> String {
        format!("{n:040x}")
    }

    fn git(dir: &std::path::Path, args: &[&str]) {
        let status = std::process::Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?} failed");
    }

    /// A real repository with a base commit followed by one commit per entry
    /// in `authors`, each carrying an `Agent-Bus-Agent` trailer per name.
    ///
    /// This replaces a `MockGit` helper that scripted `rev-list`, `show` and
    /// `interpret-trailers`. Two reasons it is better rather than merely
    /// different: the mocked `interpret-trailers` accepted any line
    /// containing `": "`, which is far more permissive than git's real
    /// trailer rules, so the tests were validating against a parser that does
    /// not exist; and `commits_between_first_parent_exclusive` now walks the
    /// object database in-process, which a subprocess mock cannot intercept
    /// at all.
    ///
    /// Returns the repository, the base commit, the tip, and the commits
    /// introduced between them in order.
    fn repo_with_authored_chain(
        authors: &[&[&str]],
    ) -> (tempfile::TempDir, String, String, Vec<String>) {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        git(path, &["init", "--quiet", "-b", "main"]);
        git(path, &["config", "user.email", "test@example.com"]);
        git(path, &["config", "user.name", "Test"]);
        std::fs::write(path.join("base.txt"), "base\n").unwrap();
        git(path, &["add", "-A"]);
        git(path, &["commit", "-q", "-m", "base"]);
        let base = crate::gitrepo::rev_parse(path, "HEAD").unwrap();

        let mut introduced = Vec::new();
        for (n, names) in authors.iter().enumerate() {
            std::fs::write(path.join(format!("f{n}.txt")), format!("content {n}\n")).unwrap();
            git(path, &["add", "-A"]);
            // A subject paragraph, a blank line, then a contiguous trailer
            // block -- the shape git actually recognizes.
            let mut message = format!("change {n}\n\n");
            for name in names.iter() {
                message.push_str(&format!("Agent-Bus-Agent: {name}\n"));
            }
            git(path, &["commit", "-q", "-m", &message]);
            introduced.push(crate::gitrepo::rev_parse(path, "HEAD").unwrap());
        }
        let tip = crate::gitrepo::rev_parse(path, "HEAD").unwrap();
        (dir, base, tip, introduced)
    }

    #[test]
    fn verify_authorship_rejects_empty_introduced_range() {
        let (repo, base, _tip, _c) = repo_with_authored_chain(&[]);
        let bob = a("bob");
        // base..base introduces nothing.
        let err = verify_authorship(repo.path(), &bob, &BTreeSet::new(), &base, &base).unwrap_err();
        assert!(err.to_string().contains("introduces no content"), "{err}");
    }

    #[test]
    fn verify_authorship_rejects_missing_author_trailer() {
        let (repo, base, tip, _c) = repo_with_authored_chain(&[&[]]);
        let bob = a("bob");
        let err = verify_authorship(repo.path(), &bob, &BTreeSet::new(), &base, &tip).unwrap_err();
        assert!(
            err.to_string().contains("has no Agent-Bus-Agent trailer"),
            "{err}"
        );
    }

    #[test]
    fn verify_authorship_rejects_reviewer_authored_commit() {
        let (repo, base, tip, _c) = repo_with_authored_chain(&[&["bob"]]);
        let bob = a("bob");
        let expected: BTreeSet<Agent> = [bob.clone()].into_iter().collect();
        let err = verify_authorship(repo.path(), &bob, &expected, &base, &tip).unwrap_err();
        assert!(err.to_string().contains("ineligible to merge"), "{err}");
    }

    #[test]
    fn verify_authorship_rejects_author_mismatch() {
        let (repo, base, tip, _c) = repo_with_authored_chain(&[&["carol"]]);
        let bob = a("bob");
        let expected: BTreeSet<Agent> = [a("alice")].into_iter().collect();
        let err = verify_authorship(repo.path(), &bob, &expected, &base, &tip).unwrap_err();
        assert!(
            err.to_string().contains("do not match nomination authors"),
            "{err}"
        );
    }

    #[test]
    fn verify_authorship_succeeds_and_returns_introduced_commits() {
        let (repo, base, tip, commits) = repo_with_authored_chain(&[&["alice"], &["alice"]]);
        let bob = a("bob");
        let expected: BTreeSet<Agent> = [a("alice")].into_iter().collect();
        let introduced = verify_authorship(repo.path(), &bob, &expected, &base, &tip).unwrap();
        let newest_first: Vec<String> = commits.iter().rev().cloned().collect();
        assert_eq!(
            introduced, newest_first,
            "`git rev-list` order: newest first, exclusive of the base"
        );
    }

    #[test]
    fn verify_authorship_accepts_multiple_authors_across_commits() {
        let (repo, base, tip, commits) = repo_with_authored_chain(&[&["alice"], &["carol"]]);
        let bob = a("bob");
        let expected: BTreeSet<Agent> = [a("alice"), a("carol")].into_iter().collect();
        let introduced = verify_authorship(repo.path(), &bob, &expected, &base, &tip).unwrap();
        let newest_first: Vec<String> = commits.iter().rev().cloned().collect();
        assert_eq!(introduced, newest_first);
    }

    /// Two roots in one repository share no history, so they have zero merge
    /// bases -- the other side of "exactly one" from the ordinary case.
    #[test]
    fn reconstruct_candidate_rejects_zero_merge_bases_between_unrelated_roots() {
        let (repo, base, _tip, _c) = repo_with_authored_chain(&[&["alice"]]);
        let bob = a("bob");
        // A second, unrelated root commit in the same repository.
        git(repo.path(), &["checkout", "--quiet", "--orphan", "other"]);
        std::fs::write(repo.path().join("other.txt"), "other\n").unwrap();
        git(repo.path(), &["add", "-A"]);
        git(repo.path(), &["commit", "-q", "-m", "unrelated root"]);
        let other = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();

        let err = reconstruct_candidate(repo.path(), &base, &other, &bob).unwrap_err();
        assert!(
            err.to_string()
                .contains("do not have exactly one merge base"),
            "{err}"
        );
    }

    /// A revision that names no object must fail loudly rather than being
    /// treated as an empty history.
    #[test]
    fn reconstruct_candidate_rejects_an_unknown_revision() {
        let (repo, base, _tip, _c) = repo_with_authored_chain(&[&["alice"]]);
        let bob = a("bob");
        let err = reconstruct_candidate(repo.path(), &base, &hash(9), &bob).unwrap_err();
        assert!(err.to_string().contains("does not name an object"), "{err}");
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
