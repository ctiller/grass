//! Turning locally accepted commits into remotely visible facts, and the
//! local receipt naming what actually landed
//! (docs/AGENT_COORDINATION_EVOLUTION.md section 2.3-2.4): "An event becomes
//! cross-box visible and usable by product merge gates only after the
//! coordinator records a remote publication receipt naming the accepted
//! remote ref tips." A local stream/registry commit (`stream.rs`,
//! `registry.rs`) is only a *local acceptance receipt* -- this module is
//! what promotes it further.
//!
//! The coordinator prefers one atomic multi-ref push when a batch spans
//! several refs that must become visible together. If the remote rejects
//! that -- because it lacks atomic-transaction support, or because any one
//! ref in the batch is no longer a fast-forward -- git guarantees no ref in
//! the atomic attempt moved, so it is always safe to fall back to pushing
//! `updates` one at a time in the caller-supplied order and stop at the
//! first rejection: "publishes prerequisite refs first and dependent refs
//! only after observing their receipts... never a dependent event without
//! its causes." `updates` must therefore already be given in dependency
//! order (registry epoch before the stream events it authorizes, or a
//! referenced agent's stream before the event that cites it).

use crate::error::AbResult;
use crate::scalars::ObjectId;
use std::collections::BTreeMap;
use std::path::Path;

/// One ref this publication batch wants to move to `new`. Whether it is a
/// fast-forward of the remote's current value (an update) or the ref does
/// not exist there yet (a creation) is decided remotely -- there is no
/// separate flag here, matching how `git push` itself treats the two cases.
#[derive(Debug, Clone)]
pub struct RefUpdate {
    pub refname: String,
    pub new: ObjectId,
}

impl RefUpdate {
    pub fn new(refname: impl Into<String>, new: ObjectId) -> Self {
        RefUpdate {
            refname: refname.into(),
            new,
        }
    }

    fn refspec(&self) -> String {
        format!("{}:{}", self.new.as_str(), self.refname)
    }
}

/// What actually reached the remote, versus what was attempted and refused,
/// versus what the batch never even tried because an earlier prerequisite
/// in the same batch failed first. A crash or partial rejection can leave
/// all three non-empty; only `published` is authority any other agent may
/// rely on.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PublicationReceipt {
    pub published: BTreeMap<String, ObjectId>,
    pub rejected: Vec<String>,
    pub not_attempted: Vec<String>,
}

impl PublicationReceipt {
    pub fn is_complete(&self, updates: &[RefUpdate]) -> bool {
        updates
            .iter()
            .all(|u| self.published.get(&u.refname) == Some(&u.new))
    }
}

/// Publish `updates`, preferring one atomic transaction and falling back to
/// dependency-ordered sequential pushes on any atomic failure. Returns the
/// receipt naming exactly what landed; it never errors on a rejected or
/// partially published batch -- rejection is ordinary coordinator policy
/// input (retry, re-batch, or surface to the author), not a crate-level
/// failure. It surfaces `Err` only for a `git` invocation that could not be
/// run at all.
pub fn publish(repo: &Path, remote: &str, updates: &[RefUpdate]) -> AbResult<PublicationReceipt> {
    if updates.is_empty() {
        return Ok(PublicationReceipt::default());
    }
    if updates.len() == 1 {
        return publish_sequential(repo, remote, updates);
    }

    let refspecs: Vec<String> = updates.iter().map(RefUpdate::refspec).collect();
    let out = crate::gitrepo::push_refspecs(repo, remote, true, &refspecs)?;
    if out.success {
        let published = updates
            .iter()
            .map(|u| (u.refname.clone(), u.new.clone()))
            .collect();
        return Ok(PublicationReceipt {
            published,
            rejected: Vec::new(),
            not_attempted: Vec::new(),
        });
    }

    publish_sequential(repo, remote, updates)
}

/// Push `updates` one ref at a time in the given order, stopping at the
/// first rejection so nothing dependent on a failed prerequisite is ever
/// attempted.
fn publish_sequential(
    repo: &Path,
    remote: &str,
    updates: &[RefUpdate],
) -> AbResult<PublicationReceipt> {
    let mut receipt = PublicationReceipt::default();
    let mut stopped = false;
    for u in updates {
        if stopped {
            receipt.not_attempted.push(u.refname.clone());
            continue;
        }
        let out = crate::gitrepo::push_refspecs(repo, remote, false, &[u.refspec()])?;
        if out.success {
            receipt.published.insert(u.refname.clone(), u.new.clone());
        } else {
            receipt.rejected.push(u.refname.clone());
            stopped = true;
        }
    }
    Ok(receipt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use std::process::Command;

    fn git(dir: &Path, args: &[&str]) {
        let status = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .status()
            .unwrap();
        assert!(status.success(), "git {args:?} failed in {}", dir.display());
    }

    fn oid(dir: &Path, rev: &str) -> ObjectId {
        ObjectId::parse(crate::gitrepo::rev_parse(dir, rev).unwrap()).unwrap()
    }

    /// A bare "origin" plus a clone with one commit already pushed to
    /// `main`, so tests can create and update refs against a real remote
    /// without a network round trip.
    struct Fixture {
        _origin: tempfile::TempDir,
        clone: tempfile::TempDir,
        origin_path: PathBuf,
    }

    impl Fixture {
        fn new() -> Self {
            let origin = tempfile::tempdir().unwrap();
            git(origin.path(), &["init", "--quiet", "--bare", "-b", "main"]);

            let clone = tempfile::tempdir().unwrap();
            git(
                clone.path(),
                &["clone", "--quiet", &origin.path().to_string_lossy(), "."],
            );
            git(clone.path(), &["config", "user.email", "test@example.com"]);
            git(clone.path(), &["config", "user.name", "Test"]);
            std::fs::write(clone.path().join("README.md"), "hello\n").unwrap();
            git(clone.path(), &["add", "README.md"]);
            git(clone.path(), &["commit", "-q", "-m", "initial"]);
            git(clone.path(), &["push", "-q", "origin", "main"]);

            Fixture {
                origin_path: origin.path().to_path_buf(),
                _origin: origin,
                clone,
            }
        }

        fn dir(&self) -> &Path {
            self.clone.path()
        }

        fn remote(&self) -> String {
            self.origin_path.to_string_lossy().to_string()
        }

        /// A commit reachable from HEAD's tree, suitable as a brand-new
        /// ref's target -- distinct commits per label so refs don't collide.
        fn new_commit(&self, label: &str) -> ObjectId {
            std::fs::write(self.dir().join(format!("{label}.txt")), label).unwrap();
            git(self.dir(), &["add", &format!("{label}.txt")]);
            git(self.dir(), &["commit", "-q", "-m", label]);
            oid(self.dir(), "HEAD")
        }
    }

    #[test]
    fn publish_is_a_noop_on_an_empty_batch() {
        let fx = Fixture::new();
        let receipt = publish(fx.dir(), &fx.remote(), &[]).unwrap();
        assert_eq!(receipt, PublicationReceipt::default());
    }

    #[test]
    fn publish_atomically_creates_two_new_refs() {
        let fx = Fixture::new();
        let a = fx.new_commit("a");
        let b = fx.new_commit("b");
        let updates = vec![
            RefUpdate::new("refs/heads/agent-events/alice", a.clone()),
            RefUpdate::new("refs/heads/agent-events/bob", b.clone()),
        ];
        let receipt = publish(fx.dir(), &fx.remote(), &updates).unwrap();
        assert!(receipt.is_complete(&updates));
        assert!(receipt.rejected.is_empty());
        assert!(receipt.not_attempted.is_empty());
        assert_eq!(
            crate::gitrepo::rev_parse(&fx.origin_path, "refs/heads/agent-events/alice").unwrap(),
            a.into_string()
        );
    }

    #[test]
    fn publish_fast_forwards_an_existing_ref() {
        let fx = Fixture::new();
        let first = fx.new_commit("first");
        publish(
            fx.dir(),
            &fx.remote(),
            &[RefUpdate::new("refs/heads/agent-events/alice", first)],
        )
        .unwrap();

        let second = fx.new_commit("second");
        let receipt = publish(
            fx.dir(),
            &fx.remote(),
            &[RefUpdate::new(
                "refs/heads/agent-events/alice",
                second.clone(),
            )],
        )
        .unwrap();
        assert_eq!(
            receipt.published.get("refs/heads/agent-events/alice"),
            Some(&second)
        );
    }

    /// A remote-side non-fast-forward on one ref in an atomic batch must
    /// leave every ref in that attempt untouched, then the sequential
    /// fallback must publish the safe prefix and stop before the rejected
    /// ref -- never touching the (perfectly fine) ref after it.
    #[test]
    fn a_stale_ref_in_the_batch_falls_back_and_stops_at_the_rejection() {
        let fx = Fixture::new();

        // Advance origin's `charlie` ref out from under this clone's
        // knowledge, so this batch's own `charlie` update is stale.
        let other_clone = tempfile::tempdir().unwrap();
        git(other_clone.path(), &["clone", "--quiet", &fx.remote(), "."]);
        git(
            other_clone.path(),
            &["config", "user.email", "other@example.com"],
        );
        git(other_clone.path(), &["config", "user.name", "Other"]);
        std::fs::write(other_clone.path().join("interloper.txt"), "x").unwrap();
        git(other_clone.path(), &["add", "interloper.txt"]);
        git(other_clone.path(), &["commit", "-q", "-m", "interloper"]);
        git(
            other_clone.path(),
            &[
                "push",
                "-q",
                &fx.remote(),
                "HEAD:refs/heads/agent-events/charlie",
            ],
        );

        let a = fx.new_commit("a");
        // `charlie`'s update below does not build on the interloper commit
        // that is now on the remote, so it is a genuine non-fast-forward.
        let stale_charlie = fx.new_commit("stale-charlie");
        let c = fx.new_commit("c");

        let updates = vec![
            RefUpdate::new("refs/heads/agent-events/alice", a.clone()),
            RefUpdate::new("refs/heads/agent-events/charlie", stale_charlie),
            RefUpdate::new("refs/heads/agent-events/carol", c),
        ];
        let receipt = publish(fx.dir(), &fx.remote(), &updates).unwrap();

        assert_eq!(receipt.published.len(), 1);
        assert_eq!(
            receipt.published.get("refs/heads/agent-events/alice"),
            Some(&a)
        );
        assert_eq!(receipt.rejected, vec!["refs/heads/agent-events/charlie"]);
        assert_eq!(receipt.not_attempted, vec!["refs/heads/agent-events/carol"]);
    }

    #[test]
    fn a_single_update_batch_skips_atomic_and_still_publishes() {
        let fx = Fixture::new();
        let a = fx.new_commit("a");
        let updates = vec![RefUpdate::new("refs/heads/agent-events/alice", a.clone())];
        let receipt = publish(fx.dir(), &fx.remote(), &updates).unwrap();
        assert!(receipt.is_complete(&updates));
    }
}
