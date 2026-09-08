//! End-to-end checks on the `axiom-audit` binary's refusal to audit nothing.
//!
//! The unit tests in the binary cover [`zero_modules_message`]'s wording. Wording is
//! not the behaviour: a build that deleted the guard and kept the function passed
//! every one of them, which a mutation run found. What has to be pinned is that the
//! *process* exits non-zero and says so, so these tests run the built binary.
//!
//! They stop before Lean is reached, which is what makes them cheap enough to sit in
//! the fast job. `.github/workflows/library.yml` runs `cargo test` before it installs
//! the toolchain, so `lake` is absent there; the assertions below are written to hold
//! whether it is present or not.

use std::fs;
use std::path::Path;
use std::process::Command;

/// Run the binary with `dir` as its working directory.
fn run_in(dir: &Path) -> (bool, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_axiom-audit"))
        .current_dir(dir)
        .output()
        .expect("the binary under test should be runnable");
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&output.stderr));
    (output.status.success(), text)
}

/// The failure this port exists to make impossible, checked on the process rather
/// than on the message it would have printed.
#[test]
fn a_tree_with_no_library_is_refused_by_the_process_and_not_reported_clean() {
    let dir = tempfile::tempdir().unwrap();
    let (ok, text) = run_in(dir.path());
    assert!(!ok, "an empty scan must not exit 0; output was:\n{text}");
    assert!(text.contains("audited nothing"), "{text}");
    assert!(text.contains("Grass/"), "{text}");
    // Naming the directory is what turns the failure into a diagnosis.
    assert!(
        text.contains(&dir.path().display().to_string()),
        "the refusal must name the directory it looked in; output was:\n{text}"
    );
    assert!(text.contains("repository root"), "{text}");
}

/// `Grass/` present but holding nothing the audit can import is the same failure.
#[test]
fn a_library_directory_with_no_lean_sources_is_refused() {
    let dir = tempfile::tempdir().unwrap();
    fs::create_dir(dir.path().join("Grass")).unwrap();
    fs::write(dir.path().join("Grass/README.md"), "not a module\n").unwrap();
    let (ok, text) = run_in(dir.path());
    assert!(!ok, "output was:\n{text}");
    assert!(text.contains("audited nothing"), "{text}");
}

/// The other half of the pair: the guard must be conditional.
///
/// A guard that fires unconditionally would satisfy both tests above while refusing
/// every real tree, so this pins that a tree with a module in it gets *past* the
/// empty-scan refusal. Where it gets to depends on whether `lake` is on `PATH`, which
/// is why the assertion is about which failure it is rather than about success.
#[test]
fn a_tree_with_a_module_gets_past_the_empty_scan_refusal() {
    let dir = tempfile::tempdir().unwrap();
    fs::create_dir(dir.path().join("Grass")).unwrap();
    fs::write(dir.path().join("Grass/Probe.lean"), "def x := 1\n").unwrap();
    let (_, text) = run_in(dir.path());
    assert!(
        !text.contains("audited nothing"),
        "a tree with a module must not be refused as an empty scan; output was:\n{text}"
    );
}

/// A module name the generated import list could not carry is refused by name,
/// before Lean is asked to parse a file the reader never sees.
#[test]
fn a_module_name_that_cannot_be_imported_is_refused_by_name() {
    let dir = tempfile::tempdir().unwrap();
    fs::create_dir(dir.path().join("Grass")).unwrap();
    fs::write(dir.path().join("Grass/not-a-name.lean"), "def x := 1\n").unwrap();
    let (ok, text) = run_in(dir.path());
    assert!(!ok, "output was:\n{text}");
    assert!(text.contains("not-a-name"), "{text}");
    assert!(text.contains("without quoting"), "{text}");
}
