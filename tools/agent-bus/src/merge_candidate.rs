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

/// The exact commit message every candidate carries (AGENT_REVIEW.md
/// section 7). Named once so the side that *writes* it
/// ([`reconstruct_candidate`]) and the side that *checks* it
/// ([`verify_candidate_object`]) can never drift apart.
pub(crate) fn candidate_message(reviewer: &Agent) -> String {
    format!("agent-bus candidate\n\nAgent-Bus-Reviewer: {reviewer}\n")
}

/// Builds the candidate commit `cli::prepare_merge` publishes for
/// `(previous_main, reviewed_commit, reviewer)` (AGENT_REVIEW.md section 7).
///
/// **Construction only.** This is the one operation in the crate whose output
/// can depend on the installed `git` -- it runs the merge engine (`git
/// merge-tree --write-tree`, ORT) -- and after g-design:249 it has exactly
/// one caller: `prepare-merge`, which *may* use whatever git the reviewer's
/// host has. Validators must not call it. They read the immutable candidate
/// object instead, through [`verify_candidate_object`], because rebuilding
/// the merge locally is what made a reader's git version an authority over
/// history somebody else already published.
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
    let message = candidate_message(reviewer);
    crate::gitrepo::commit_tree_deterministic(
        repo,
        &tree,
        &[previous_main, reviewed_commit],
        &message,
    )
}

/// Makes the candidate object resolvable in `repo`, fetching its immutable
/// tag from `remote` if this checkout does not already have it.
///
/// Best-effort by design: the object may already be present locally (this
/// genuinely is the checkout that ran `prepare-merge`), and a failed fetch is
/// not by itself the interesting fact -- what matters is whether the object
/// resolves afterwards. If it still does not, the error says what to do,
/// rather than leaving a downstream command to surface a raw "bad object".
pub(crate) fn fetch_candidate_tag(
    repo: &Path,
    remote: &str,
    reviewer: &Agent,
    candidate: &str,
) -> AbResult<()> {
    let tag = candidate_tag_name(reviewer, candidate);
    let _ =
        crate::gitrepo::fetch_refspecs(repo, remote, &[format!("refs/tags/{tag}:refs/tags/{tag}")]);
    if crate::gitrepo::rev_parse_opt(repo, candidate)?.is_none() {
        return Err(invalid(format!(
            "candidate {candidate} is not fetchable in this checkout, even after trying to fetch \
             refs/tags/{tag} from {remote} -- has `prepare-merge` been run and its candidate tag \
             actually reached {remote}?"
        )));
    }
    Ok(())
}

/// Validates the candidate **as the object that is actually there**, with no
/// local reconstruction (g-design:249).
///
/// Validation used to rebuild the merge with this host's `git merge-tree
/// --write-tree` and require the result to equal the published candidate.
/// That is what made an installed git version protocol authority: an honest
/// reviewer on 2.53.0 and an honest coordinator on 2.51.0 could disagree
/// about a merge neither had any reason to redo, and the fix on offer was to
/// make every host in the fleet compile one particular git. The repository
/// owner rejected that: agents need only ordinary `git pull`/`fetch` and
/// non-force push.
///
/// So this binds to the immutable candidate instead. Everything the old
/// reconstruction guaranteed that does not require re-running the merge
/// engine is still guaranteed, and checked directly against the object:
///
///  - **the tag** -- `previous_main`/`reviewed_commit` have exactly one merge
///    base, so the candidate names a merge that is well defined at all
///    (AGENT_REVIEW.md section 7, "It requires one merge base");
///  - **the parents** -- exactly `[previous_main, reviewed_commit]`, in that
///    order, so the candidate merges the reviewed commit into the authorized
///    base and nothing else;
///  - **the message and trailer** -- byte-identical to
///    [`candidate_message`], so the candidate carries exactly one
///    `Agent-Bus-Reviewer` trailer naming this reviewer and no smuggled
///    additional trailers.
///
/// The candidate's **tree** is bound by the object id itself -- every host
/// verifies the same immutable object rather than its own re-derivation of
/// one -- and bounded by scope, which callers check with
/// [`verify_candidate_scope`].
///
/// What is deliberately *not* checked is that the tree is the ORT merge of
/// the two parents, and that the commit carries the deterministic
/// identity/timestamp `commit_tree_deterministic` writes. Both were
/// side-effects of the identity comparison, and both are exactly the
/// reader-build-sensitive part: the first cannot be answered without running
/// a merge engine, and the second only ever mattered because the answer had
/// to hash to a predicted id.
pub(crate) fn verify_candidate_object(
    repo: &Path,
    reviewer: &Agent,
    previous_main: &str,
    reviewed_commit: &str,
    candidate: &str,
) -> AbResult<()> {
    if crate::gitrepo::merge_base_count(repo, previous_main, reviewed_commit)? != 1 {
        return Err(invalid(
            "previous_main and reviewed_commit do not have exactly one merge base",
        ));
    }
    let parents = crate::gitrepo::parents_of(repo, candidate)?;
    if parents != vec![previous_main.to_string(), reviewed_commit.to_string()] {
        return Err(invalid(
            "candidate parents do not match previous_main/reviewed_commit in order",
        ));
    }
    // Checked before the exact message, so a candidate whose trailer is the
    // thing that is wrong says which trailer rather than printing two whole
    // messages and leaving the reader to spot the difference.
    let trailers = crate::gitrepo::commit_message_trailers(repo, candidate)?;
    let reviewer_trailers: Vec<&(String, String)> = trailers
        .iter()
        .filter(|(k, _)| k == "Agent-Bus-Reviewer")
        .collect();
    if reviewer_trailers.len() != 1 || reviewer_trailers[0].1 != reviewer.as_str() {
        return Err(invalid(
            "candidate must have exactly one matching Agent-Bus-Reviewer trailer",
        ));
    }
    let message = crate::gitrepo::commit_message(repo, candidate)?;
    let expected = candidate_message(reviewer);
    if message != expected {
        return Err(invalid(format!(
            "candidate {candidate} does not carry the exact candidate message: expected \
             {expected:?}, found {message:?}"
        )));
    }
    Ok(())
}

/// AGENT_REVIEW.md section 8: nothing the candidate changes over `from` may
/// fall outside `reviewed_scope`.
///
/// This is the content half of validating a candidate nobody rebuilds. The
/// candidate's tree is whatever the reviewer's merge produced, and this is
/// what bounds it: a candidate that touches a path the nomination never
/// covered carries content no reviewer authorized, whichever engine built it.
pub(crate) fn verify_candidate_scope(
    repo: &Path,
    from: &str,
    candidate: &str,
    reviewed_scope: &[crate::scalars::PathClaim],
) -> AbResult<()> {
    let changed = crate::gitrepo::diff_name_status(repo, from, candidate)?;
    for (_, path) in &changed {
        if !reviewed_scope
            .iter()
            .any(|p| crate::merge_ready::path_in_claim(path, p))
        {
            return Err(invalid(format!(
                "changed path {path} is outside reviewed_scope"
            )));
        }
    }
    Ok(())
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

    /// AGENT_REVIEW.md sections 3/7 require the trailer union to equal the
    /// nomination's authors *exactly* -- not merely to overlap them.
    ///
    /// Both directions matter and neither was pinned: relaxing `!=` to a
    /// disjointness test left the suite green, because the one mismatch test
    /// used author sets that were completely disjoint. A candidate naming
    /// fewer authors than the nomination claims, or more, is a different
    /// change from the one that was reviewed.
    #[test]
    fn verify_authorship_rejects_authors_that_are_a_subset_of_the_nomination() {
        let (repo, base, tip, _c) = repo_with_authored_chain(&[&["alice"]]);
        let bob = a("bob");
        let expected: BTreeSet<Agent> = [a("alice"), a("carol")].into_iter().collect();
        let err = verify_authorship(repo.path(), &bob, &expected, &base, &tip).unwrap_err();
        assert!(
            err.to_string().contains("do not match nomination authors"),
            "a candidate naming fewer authors than the nomination must be refused: {err}"
        );
    }

    #[test]
    fn verify_authorship_rejects_authors_beyond_the_nomination() {
        let (repo, base, tip, _c) = repo_with_authored_chain(&[&["alice"], &["carol"]]);
        let bob = a("bob");
        let expected: BTreeSet<Agent> = [a("alice")].into_iter().collect();
        let err = verify_authorship(repo.path(), &bob, &expected, &base, &tip).unwrap_err();
        assert!(
            err.to_string().contains("do not match nomination authors"),
            "a candidate naming an author the nomination does not must be refused: {err}"
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

    /// The *other* side of "exactly one merge base". A criss-cross history
    /// gives two, and this branch of the guard at `merge_candidate.rs`'s
    /// `merge_base_count(...) != 1` was left untested when the mock-based
    /// test that covered it was replaced with a zero-base one.
    #[test]
    fn reconstruct_candidate_rejects_multiple_merge_bases() {
        let (repo, _base, _tip, _c) = repo_with_authored_chain(&[&["alice"]]);
        let bob = a("bob");

        use crate::gitobjects::{ObjectWriter, RefStore};
        let g = crate::gitobjects::Libgit2Reader::open(repo.path()).unwrap();
        let blob = g.write_blob(b"x").unwrap();
        let tree = g.write_tree(None, &[("x.txt", blob)]).unwrap();

        // Two independent roots, then two merges of both, in opposite parent
        // order: the pair of merges has two distinct merge bases.
        let r1 = g.create_commit(&tree, &[], "root one").unwrap();
        let r2 = g.create_commit(&tree, &[], "root two").unwrap();
        let m1 = g.create_commit(&tree, &[&r1, &r2], "merge one").unwrap();
        let m2 = g.create_commit(&tree, &[&r2, &r1], "merge two").unwrap();
        let _ = &g as &dyn RefStore;

        assert_eq!(
            crate::gitrepo::merge_base_count(repo.path(), m1.as_str(), m2.as_str()).unwrap(),
            2,
            "fixture must actually produce two merge bases"
        );

        let err = reconstruct_candidate(repo.path(), m1.as_str(), m2.as_str(), &bob).unwrap_err();
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
