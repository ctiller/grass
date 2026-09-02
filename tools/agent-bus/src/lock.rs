//! Cross-process mutation lock, held outside the committed tree
//! (AGENT_BUS.md section 8: "Mutation commands acquire an operating-system
//! lock outside the committed tree").

use crate::error::{AbError, AbResult};
use fs4::FileExt;
use std::fs::{File, OpenOptions};
use std::path::{Path, PathBuf};

pub struct BusLock {
    _file: File,
    path: PathBuf,
}

impl BusLock {
    /// Acquire an exclusive advisory lock at `<repo_git_dir>/agent-bus.lock`.
    /// This lives under `.git/`, which is never part of any committed tree.
    pub fn acquire(git_dir: &Path) -> AbResult<BusLock> {
        std::fs::create_dir_all(git_dir).map_err(|e| AbError::Io {
            path: git_dir.display().to_string(),
            source: e,
        })?;
        let path = git_dir.join("agent-bus.lock");
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(false)
            .open(&path)
            .map_err(|e| AbError::Io {
                path: path.display().to_string(),
                source: e,
            })?;
        FileExt::lock_exclusive(&file)
            .map_err(|e| AbError::Git(format!("failed to lock {}: {e}", path.display())))?;
        Ok(BusLock { _file: file, path })
    }
}

impl Drop for BusLock {
    fn drop(&mut self) {
        let _ = FileExt::unlock(&self._file);
        let _ = &self.path;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;
    use std::time::Duration;

    #[test]
    fn acquire_creates_git_dir_if_missing_and_locks_successfully() {
        let tmp = tempfile::tempdir().unwrap();
        let git_dir = tmp.path().join("nested").join(".git");
        assert!(!git_dir.exists());
        let lock = BusLock::acquire(&git_dir).unwrap();
        assert!(git_dir.join("agent-bus.lock").exists());
        drop(lock);
    }

    #[test]
    fn sequential_acquire_after_drop_succeeds() {
        let tmp = tempfile::tempdir().unwrap();
        let git_dir = tmp.path().to_path_buf();

        let first = BusLock::acquire(&git_dir).unwrap();
        drop(first);

        // Must not hang or error: the OS-level lock was actually released
        // by `Drop`, not just the Rust value.
        let second = BusLock::acquire(&git_dir).unwrap();
        drop(second);
    }

    /// The realistic, hard-to-provoke-with-real-processes case this crate
    /// cares about: two `BusLock::acquire` calls contending for the same
    /// `<git_dir>/agent-bus.lock` file via two real OS file handles in one
    /// process. `acquire` blocks (via `fs4`'s blocking `lock_exclusive`)
    /// until the first lock is released, so we drive the second attempt on
    /// a background thread and assert it does *not* complete while the
    /// first lock is held, then that it completes promptly once dropped.
    #[test]
    fn concurrent_acquire_blocks_until_first_lock_is_dropped() {
        let tmp = tempfile::tempdir().unwrap();
        let git_dir = tmp.path().to_path_buf();

        let first = BusLock::acquire(&git_dir).unwrap();

        let (tx, rx) = mpsc::channel();
        let gd = git_dir.clone();
        let handle = std::thread::spawn(move || {
            let _second = BusLock::acquire(&gd).unwrap();
            tx.send(()).unwrap();
            // Keep the second lock alive until the main thread has observed
            // the completion signal, so we're not racing our own cleanup.
            std::thread::sleep(Duration::from_millis(50));
        });

        assert!(
            rx.recv_timeout(Duration::from_millis(300)).is_err(),
            "second acquire completed while the first lock was still held"
        );

        drop(first);

        rx.recv_timeout(Duration::from_secs(5))
            .expect("second acquire never completed after the first lock was released");

        handle.join().unwrap();
    }

    #[test]
    fn acquire_errors_when_a_path_component_is_blocked_by_a_file() {
        let tmp = tempfile::tempdir().unwrap();
        let blocker = tmp.path().join("blocker");
        std::fs::write(&blocker, b"not a directory").unwrap();
        // `blocker` is a regular file, so `create_dir_all` for a `.git`
        // directory *under* it can never succeed.
        let bad_git_dir = blocker.join(".git");

        // `BusLock` intentionally isn't `Debug` (it wraps a `File`), so
        // `unwrap_err()` isn't available here; match instead.
        match BusLock::acquire(&bad_git_dir) {
            Err(AbError::Io { .. }) => {}
            Err(other) => panic!("expected AbError::Io, got {other}"),
            Ok(_) => panic!("expected acquire to fail when a path component is a file"),
        }
    }

    #[test]
    fn acquire_errors_when_lock_file_path_is_a_directory() {
        let tmp = tempfile::tempdir().unwrap();
        let git_dir = tmp.path().to_path_buf();
        // Occupy the exact path `acquire` wants to open as a file.
        std::fs::create_dir_all(git_dir.join("agent-bus.lock")).unwrap();

        match BusLock::acquire(&git_dir) {
            Err(AbError::Io { .. }) => {}
            Err(other) => panic!("expected AbError::Io, got {other}"),
            Ok(_) => panic!("expected acquire to fail when the lock file path is a directory"),
        }
    }
}
