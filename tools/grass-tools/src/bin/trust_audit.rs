//! Audit the trust closure of every concrete `VerifiedProgram` in the repository.
//!
//! This is the port of `audit-trust.ps1`, which `README.md` documents as one half
//! of the primary validation command (`lake build`, then this) and which
//! `.github/workflows/library.yml` runs as "Audit verified-program trust closure".
//! It was PowerShell-only, so on a Linux developer host the documented way to
//! validate this repository could not be run at all.
//!
//! # What is being audited, and why it is not the axiom audit
//!
//! `axiom-audit` asks what each `Grass` declaration depends on. This asks a
//! different and larger question: whether the path from a `VerifiedProgram`
//! certificate to the bytes `emitProgram` hands back is closed. Four distinct ways
//! that path can be open, and all four are checked here:
//!
//! 1. **A root that is not a root.** `#audit_verified_programs` discovers concrete
//!    `VerifiedProgram` producers by unfolding even irreducible result aliases, so a
//!    certificate cannot be hidden behind a type synonym and escape the audit.
//! 2. **A certificate obtained rather than proved.** A `VerifiedProgram` reached
//!    through `Classical.choice` of a `Nonempty` axiom, or through any other
//!    container, is not a proof that a program is correct; it is an assertion that
//!    one exists. Every declaration in the certificate-sensitive closure is audited
//!    for its axioms, across arbitrarily named imported modules.
//! 3. **A compiled definition that is not the proved one.** Every theorem in this
//!    repository is about the definition the kernel sees, while the artefact a user
//!    runs is the compiled one. `@[implemented_by]`, `@[extern]` and `@[csimp]` are
//!    the three ways to separate them, and the audit follows the *runtime*
//!    dependency closure downstream of emission to reject all three.
//! 4. **An attribute whose scope has expired.** A `csimp` substitution introduced
//!    with `attribute [local csimp]` is gone from the environment by the time a
//!    downstream module imports the result, so the audit has to reason about
//!    participating module cohorts and persisted compiler dependency modules rather
//!    than about the attribute state it can see.
//!
//! On top of the audit itself, the named public theorem roots in [`DECLARATIONS`]
//! are checked as an explicit manifest with `#print axioms`, and every axiom
//! reported must be in [`ALLOWED_AXIOMS`].
//!
//! `docs/FOUNDATION.md` §3 supplies that allowlist and is the trust boundary: the
//! three reviewed logical-foundation constants and nothing else. The build's
//! `warningAsError = true` independently rejects `sorry`; this rejects everything
//! that reaches the same place without a warning.
//!
//! # The audit checks itself, and that is most of this file
//!
//! Roughly two thirds of `audit-trust.ps1` is not the audit. It is ten adversarial
//! probes that each construct a way to smuggle an unverified artefact past
//! `Grass/Trust/Audit.lean` and require the audit to notice. They exist because the
//! audit is a Lean meta-program over an environment, and a meta-program that has
//! quietly stopped discovering roots reports the same clean line as one that is
//! working -- with the difference that it now certifies nothing. Each probe is a
//! falsification of the audit, run every time the audit runs.
//!
//! Six of them must make the audit *fail*, and the probe fails if the audit
//! succeeds. Four of them must make the audit *succeed* while naming something
//! specific, and the probe fails if the name is absent. See [`Probes`] for the
//! individual rationales; they are carried over one for one, and none is dropped.
//!
//! Three of the probes are compiled to `.olean` and imported rather than elaborated
//! in place, because the defect they model only exists across a module boundary:
//! an `@[extern]` attribute or an expired `local csimp` is a property of what a
//! module *persisted*, and a single-file probe cannot express it.
//!
//! # Why a Rust program that writes Lean
//!
//! The same reason as `axiom-audit`. The environment queries have no answer outside
//! Lean; the judgement -- which axioms are permitted, which probes must fail, what
//! counts as having examined anything -- does not need Lean and is unit-tested here
//! without a build. The generated Lean is elaborated by `lake env lean` from the
//! repository root, exactly as the PowerShell invoked it.
//!
//! # An audit of nothing is not a clean audit
//!
//! `audit-trust.ps1` could report success having audited no executable test module
//! at all. Its last line reads "Trust audit passed for 57 declaration(s) and 0
//! executable test module(s)", and it prints exactly that -- exit 0 -- whenever
//! `Tests/` yields no module whose source matches [`TOP_LEVEL_MAIN_PATTERN`]. An
//! emptied test tree, a test root pointed at the wrong directory (the script took
//! `-TestSourceRoot` from the command line), or a change to how executable tests
//! declare their entrypoint all produce it, and none of them produces a finding.
//! Those modules are audited *only* in that loop -- they cannot be imported
//! together, since they all declare `main` -- so their entire trust closure goes
//! unexamined while the run reads as assurance.
//!
//! [`verdict`] refuses that, and refuses the same shape on the library side. See
//! `an_audit_with_no_executable_test_modules_is_refused`.
//!
//! # Deliberate departures from the PowerShell, each of them a defect report
//!
//! - **The roots, the declaration manifest and the axiom allowlist are constants.**
//!   `audit-trust.ps1` took all four as parameters, so `-AllowedAxiom sorryAx`, or
//!   `-Declaration` naming one trivial theorem, turned the gate off from the
//!   command line without editing a file. For a trust boundary that is a defect,
//!   not a convenience: `axiom-audit` states in its own allowlist comment that
//!   changing it "is a trust-boundary change and requires the review that section
//!   demands, not an edit here". This tool takes no arguments.
//!
//! - **The ordinal-comparison self-test is a unit test, not a runtime probe.** The
//!   original ran [`rejected_axioms`] against a case variant on every invocation,
//!   because PowerShell's case-sensitive operators are culture-sensitive and can
//!   equate distinct Unicode spellings. Rust's `str` equality is byte equality by
//!   the language, so the runtime probe would assert a property of the compiler.
//!   The test is kept, as `the_allowlist_comparison_is_ordinal`.
//!
//! - **Probe files are removed on every exit path, including a panic.** The
//!   original's `finally` did not cover the process being killed, and the files it
//!   writes are `.lean` files at the repository root -- one of which declares
//!   `axiom boxedVerifiedProgram : Nonempty (VerifiedProgram ...)`. Neither the
//!   root nor `*.lean` is in `.gitignore`, so an interrupted run leaves an
//!   axiom-bearing source file staged-able at the top of the tree. That hazard is
//!   reported, not fixed -- a `Drop` guard is no better than `finally` against
//!   `SIGKILL` -- but the names are now prefixed so a leftover is recognisable.
//!
//! - **Diagnostics accompany their finding.** The original wrote a failing probe's
//!   Lean output to the host stream and the finding to the error stream, so the two
//!   arrived separately. Both are now in the message.
//!
//! Exit status is 1 on any rejected axiom, on any probe that does not behave as
//! required, on a declaration manifest that does not report in full, and on an
//! empty scan.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::atomic::{AtomicU64, Ordering};

use regex::Regex;

/// The library source roots, whose modules are imported into one aggregate audit.
const LIBRARY_ROOTS: &[&str] = &["Grass"];

/// The test source roots. Modules declaring a top-level `main` are audited
/// individually; see [`TOP_LEVEL_MAIN_PATTERN`].
const TEST_ROOTS: &[&str] = &["Tests"];

/// The reviewed logical-foundation allowlist.
///
/// Exactly the three constants `docs/FOUNDATION.md` §3 permits, by their toolchain
/// declaration names. Adding to this list is a trust-boundary change and requires
/// the review that section demands, not an edit here -- which is why, unlike the
/// PowerShell's `-AllowedAxiom`, it cannot be supplied from the command line.
const ALLOWED_AXIOMS: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

/// The public theorem roots checked as an explicit manifest.
///
/// The audit command discovers what it can reach; this list is the part that is
/// stated rather than discovered, so that a refactor which stops a theorem being
/// reachable fails the gate instead of quietly shrinking it. Carried over from
/// `audit-trust.ps1` unchanged and in its order. [`verdict`] requires one
/// `#print axioms` report per entry, so a name that stops existing is a failure
/// rather than a silently shorter audit.
const DECLARATIONS: &[&str] = &[
    "Grass.StableId.render_of_empty_namespace",
    "Grass.RequirementKind.extension_injective",
    "Grass.DemandCertificateFamily.get",
    "Grass.ObservationProjection.ext",
    "Grass.ObservationProjection.identity_project",
    "Grass.ObservationProjection.comp_project",
    "Grass.ObservationProjection.identity_comp",
    "Grass.ObservationProjection.comp_identity",
    "Grass.ObservationProjection.comp_assoc",
    "Grass.RelationalSystem.Steps.trans",
    "Grass.RelationalSystem.Steps.graphExtends",
    "Grass.RelationalSystem.InfiniteContinuation.ext",
    "Grass.RelationalSystem.InfiniteContinuation.graphExtendsAt",
    "Grass.RelationalSystem.InfiniteContinuation.prefixSteps",
    "Grass.RelationalSystem.Runs.initialValid",
    "Grass.RelationalSystem.Runs.steps",
    "Grass.RelationalSystem.Runs.ofInitialSteps",
    "Grass.RelationalSystem.Runs.append",
    "Grass.RelationalSystem.Runs.graphExtends",
    "Grass.RelationalSystem.ExecutionPrefix.ext",
    "Grass.RelationalSystem.ExecutionPrefix.append_refl",
    "Grass.RelationalSystem.ExecutionPrefix.append_assoc",
    "Grass.RelationalSystem.ExecutionPrefix.step_eq_append",
    "Grass.BehaviorRefinement.ext",
    "Grass.BehaviorRefinement.refl_trans",
    "Grass.BehaviorRefinement.trans_refl",
    "Grass.BehaviorRefinement.trans_assoc",
    "Grass.BehaviorRefinement.mapSteps",
    "Grass.BehaviorRefinement.mapInfinite",
    "Grass.BehaviorRefinement.mapInfinite_refl",
    "Grass.BehaviorRefinement.mapInfinite_trans",
    "Grass.BehaviorRefinement.mapCompletion",
    "Grass.BehaviorRefinement.mapCompletion_refl",
    "Grass.BehaviorRefinement.mapCompletion_trans",
    "Grass.BehaviorRefinement.mapRuns",
    "Grass.BehaviorRefinement.mapPrefix_refl",
    "Grass.BehaviorRefinement.mapPrefix_initial",
    "Grass.BehaviorRefinement.mapPrefix_trans",
    "Grass.BehaviorRefinement.mapPrefix_step",
    "Grass.BehaviorRefinement.mapPrefix_append",
    "Grass.BehaviorRefinement.mapPrefix_events",
    "Grass.BehaviorRefinement.observe_mapPrefix",
    "Grass.BehaviorRefinement.inputOf_mapPrefix",
    "Grass.BehaviorRefinement.hasInput_mapPrefix",
    "Grass.BehaviorRefinement.terminal_mapPrefix",
    "Grass.BehaviorRefinement.mapCompletionAtPrefix",
    "Grass.BehaviorRefinement.mapCompletionAtPrefix_refl",
    "Grass.BehaviorRefinement.mapCompletionAtPrefix_trans",
    "Grass.BehaviorRefinement.preservesAcceptance",
    "Grass.VerifiedProgram.loadedBehavior_exact",
    "Grass.VerifiedProgram.loadedAdequate",
    "Grass.VerifiedProgram.sound",
    "Grass.VerifiedProgram.execution_nonempty",
    "Grass.VerifiedProgram.execution_completes",
    "Grass.VerifiedProgram.CompletionRefinement",
    "Grass.VerifiedProgram.completion_refinement_nonempty",
    "Grass.emitProgram_parses",
];

/// A top-level `def main`, which makes a test module an executable entrypoint.
///
/// Carried over verbatim, with its reasoning, from `audit-trust.ps1`:
///
/// > Executable test modules intentionally share Lean's required top-level runner
/// > name `main`, so importing two of them into one environment is impossible.
/// > Audit each such module separately below. A false positive only creates an
/// > extra audit pass; a missed entrypoint makes the aggregate import fail, so this
/// > partition cannot silently drop a module.
///
/// It is a textual test and does not know about comments or string literals, which
/// is exactly why the asymmetry above is the argument that it is safe.
const TOP_LEVEL_MAIN_PATTERN: &str =
    r"(?m)^[\t ]*(?:(?:unsafe|partial|noncomputable)[\t ]+)*def[\t ]+main(?:[\t ]|:)";

/// `'X' does not depend on any axioms`, as `#print axioms` prints it.
const NO_AXIOMS_PATTERN: &str = r"^'[^']+' does not depend on any axioms$";

/// `'X' depends on axioms: [a, b]`, as `#print axioms` prints it.
const AXIOMS_PATTERN: &str = r"^'[^']+' depends on axioms: \[(.*)\]$";

// ---------------------------------------------------------------------------
// The judgement, which needs no Lean.
// ---------------------------------------------------------------------------

/// What one `#print axioms` line said.
#[derive(Debug, Clone, PartialEq, Eq)]
enum AxiomReport {
    /// `'X' does not depend on any axioms`.
    None,
    /// `'X' depends on axioms: [...]`, with the bracket contents split and trimmed.
    Depends(Vec<String>),
    /// Anything else Lean printed. Passed through to the reader untouched, as the
    /// original did, because a diagnostic is not a report and must not be judged as
    /// one.
    Other,
}

/// Read one line of Lean output as an axiom report.
fn classify_axiom_line(no_axioms: &Regex, axioms: &Regex, line: &str) -> AxiomReport {
    if no_axioms.is_match(line) {
        return AxiomReport::None;
    }
    match axioms.captures(line) {
        Some(captured) => AxiomReport::Depends(
            captured[1]
                .split(',')
                .map(|axiom| axiom.trim().to_string())
                .collect(),
        ),
        None => AxiomReport::Other,
    }
}

/// The axioms in `used` that are not in `allowed`, compared ordinally.
///
/// The original's comment is the whole point of this function existing separately,
/// and it is preserved because the reasoning outlives its language:
///
/// > Lean names require ordinal equality. Even PowerShell's case-sensitive
/// > comparison operators use culture-sensitive string comparison, which can equate
/// > distinct Unicode spellings.
///
/// In Rust `==` on `&str` *is* byte comparison, so the property the PowerShell had
/// to arrange is here by construction. It is still asserted, once, in
/// `the_allowlist_comparison_is_ordinal`.
fn rejected_axioms<'a>(used: &'a [String], allowed: &[&str]) -> Vec<&'a str> {
    used.iter()
        .map(String::as_str)
        .filter(|axiom| !allowed.contains(axiom))
        .collect()
}

/// The module partition a scan of the source roots produced.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Scan {
    /// Library modules, imported together into the aggregate audit.
    library: Vec<String>,
    /// Test modules without a top-level `main`, imported alongside them.
    test: Vec<String>,
    /// Test modules with a top-level `main`, audited one at a time.
    entrypoint: Vec<String>,
}

impl Scan {
    /// Every module that goes into the aggregate import, sorted and deduplicated,
    /// as `Sort-Object -Unique` produced it.
    fn aggregate(&self) -> Vec<String> {
        let mut all: Vec<String> = self.library.iter().chain(&self.test).cloned().collect();
        all.sort();
        all.dedup();
        all
    }
}

/// Whether a scan examined enough for its verdict to mean anything.
///
/// Three ways a run can examine nothing, and the third is the one the original
/// reported as success. See the module comment.
fn verdict(scan: &Scan) -> Result<(), String> {
    if scan.library.is_empty() {
        return Err(format!(
            "trust audit: the configured library source root(s) {} contain no Lean modules, so \
             there is nothing to audit.\nRefusing to report a clean trust audit of an empty scan: \
             run this from the repository root.",
            LIBRARY_ROOTS.join(", ")
        ));
    }
    if scan.test.is_empty() && scan.entrypoint.is_empty() {
        return Err(format!(
            "trust audit: the configured test source root(s) {} contain no Lean modules, so the \
             test closure was not audited.\nRefusing to report a clean trust audit of an empty \
             scan: run this from the repository root.",
            TEST_ROOTS.join(", ")
        ));
    }
    if scan.entrypoint.is_empty() {
        return Err(format!(
            "trust audit: found {} test module(s) and not one executable entrypoint, so no \
             executable test module was audited.\nThose modules are audited only one at a time -- \
             they all declare `main` and cannot be imported together -- so a run that finds none \
             examines none of them and still reports a clean audit. Refusing to report \"0 \
             executable test module(s)\" as a pass.",
            scan.test.len()
        ));
    }
    Ok(())
}

/// The line a passing run prints.
fn passing_line(reported: usize, entrypoints: usize) -> String {
    format!("Trust audit passed for {reported} declaration(s) and {entrypoints} executable test module(s).")
}

// ---------------------------------------------------------------------------
// The tree walk.
// ---------------------------------------------------------------------------

/// The dotted module name a source path under the repository root denotes.
fn module_name(relative: &str) -> String {
    relative
        .strip_suffix(".lean")
        .unwrap_or(relative)
        .replace('\\', "/")
        .replace('/', ".")
}

/// Every `*.lean` file under `root`, as a `/`-separated path relative to
/// `repository`, sorted.
fn lean_sources(repository: &Path, root: &str) -> Result<Vec<String>, String> {
    let directory = repository.join(root);
    if !directory.is_dir() {
        return Err(format!(
            "trust audit: configured source root '{root}' does not exist."
        ));
    }
    let mut found = Vec::new();
    walk(&directory, root, &mut found)?;
    found.sort();
    Ok(found)
}

fn walk(directory: &Path, prefix: &str, found: &mut Vec<String>) -> Result<(), String> {
    let entries = fs::read_dir(directory)
        .map_err(|err| format!("trust audit: {}: {err}", directory.display()))?;
    for entry in entries {
        let entry = entry.map_err(|err| format!("trust audit: {}: {err}", directory.display()))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let relative = format!("{prefix}/{name}");
        let file_type = entry
            .file_type()
            .map_err(|err| format!("trust audit: {}: {err}", entry.path().display()))?;
        if file_type.is_dir() {
            walk(&entry.path(), &relative, found)?;
        } else if name.ends_with(".lean") {
            found.push(relative);
        }
    }
    Ok(())
}

/// Partition the source roots into the three module sets.
fn scan_sources(repository: &Path) -> Result<Scan, String> {
    let main = Regex::new(TOP_LEVEL_MAIN_PATTERN).expect("constant");
    let mut scan = Scan::default();
    for root in LIBRARY_ROOTS {
        for relative in lean_sources(repository, root)? {
            scan.library.push(module_name(&relative));
        }
    }
    for root in TEST_ROOTS {
        for relative in lean_sources(repository, root)? {
            let source = fs::read_to_string(repository.join(&relative))
                .map_err(|err| format!("trust audit: {relative}: {err}"))?;
            if main.is_match(&source) {
                scan.entrypoint.push(module_name(&relative));
            } else {
                scan.test.push(module_name(&relative));
            }
        }
    }
    scan.library.sort();
    scan.library.dedup();
    scan.test.sort();
    scan.test.dedup();
    scan.entrypoint.sort();
    scan.entrypoint.dedup();
    Ok(scan)
}

// ---------------------------------------------------------------------------
// Running Lean.
// ---------------------------------------------------------------------------

/// What one `lake env lean` invocation produced.
struct Run {
    ok: bool,
    /// Standard output followed by standard error, split into lines. The original
    /// merged the two streams with `2>&1` and then matched line by line; every
    /// pattern here is a single-line pattern, so the concatenation order does not
    /// change any verdict, only the order a reader sees a failure's diagnostics in.
    lines: Vec<String>,
}

impl Run {
    /// Whether any single line matches, which is what `$output -match $pattern` did
    /// over an array. Case-insensitive, because PowerShell's `-match` is.
    fn matches(&self, pattern: &Regex) -> bool {
        self.lines.iter().any(|line| pattern.is_match(line))
    }

    /// Every line, for a message that has to carry the diagnostics.
    fn transcript(&self) -> String {
        self.lines.join("\n")
    }
}

/// A distinct suffix for one run's generated module names.
///
/// The original used a fresh GUID per name so two concurrent audits in one
/// repository could not collide on the `.lean` and `.olean` files they write into
/// the working tree. Process id, wall clock and a counter give the same separation
/// without a dependency; unlike a GUID it is not unguessable, which nothing here
/// relies on.
fn nonce() -> String {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0);
    format!(
        "{:08x}{:016x}{:04x}",
        std::process::id(),
        nanos,
        COUNTER.fetch_add(1, Ordering::Relaxed)
    )
}

/// A `.lean` module written into the repository root, with its `.olean`.
///
/// Both are removed when this value is dropped, which covers an early return and a
/// panic as well as the original's `finally`. It does not cover the process being
/// killed; see the module comment.
struct RepositoryProbe {
    module: String,
    source: PathBuf,
    olean: PathBuf,
}

impl RepositoryProbe {
    /// The probe modules have to live at the repository root and their `.olean`
    /// under `.lake/build/lib/lean`, because that is what `lake env lean` puts on
    /// `LEAN_PATH`: an `import` of a module compiled anywhere else does not resolve.
    fn new(repository: &Path, kind: &str) -> Self {
        let module = format!("GrassToolsTrustAudit{kind}{}", nonce());
        Self {
            source: repository.join(format!("{module}.lean")),
            olean: repository.join(format!(".lake/build/lib/lean/{module}.olean")),
            module,
        }
    }
}

impl Drop for RepositoryProbe {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.source);
        let _ = fs::remove_file(&self.olean);
    }
}

/// The two things the audit asks of Lean.
///
/// A trait rather than an inherent impl for one reason, and it is the reason this
/// port exists in the shape it does. Six of the ten probes below pass *because*
/// their `lake env lean` exited non-zero, so the whole audit is a program that
/// spends most of its time reading failing exit statuses and must never let one
/// become its own. That is the bug `audit-trust.ps1` shipped for 39 consecutive
/// runs. Injecting the driver lets `the_success_path_exits_zero_though_its_last_
/// lean_invocation_failed` drive every probe to its passing outcome -- the last of
/// them a failing invocation -- and assert on the process exit status, without a
/// toolchain and without a repository. See that test.
trait LeanDriver {
    /// Elaborate `lines` as a throwaway file outside the tree.
    fn elaborate(&self, lines: &[String]) -> Result<Run, String>;

    /// Compile `lines` as `probe`'s module, so that a later file can `import` it.
    fn compile(&self, probe: &RepositoryProbe, lines: &[String]) -> Result<Run, String>;
}

/// Elaborates generated Lean from the repository root.
struct Lean {
    repository: PathBuf,
    scratch: tempfile::TempDir,
}

impl Lean {
    fn new(repository: &Path) -> Result<Self, String> {
        Ok(Self {
            repository: repository.to_path_buf(),
            scratch: tempfile::Builder::new()
                .prefix("grass-trust-audit")
                .tempdir()
                .map_err(|err| {
                    format!("trust audit: could not create a working directory: {err}")
                })?,
        })
    }
}

impl LeanDriver for Lean {
    fn elaborate(&self, lines: &[String]) -> Result<Run, String> {
        let path = self.scratch.path().join(format!("Probe{}.lean", nonce()));
        fs::write(&path, format!("{}\n", lines.join("\n")))
            .map_err(|err| format!("trust audit: could not write {}: {err}", path.display()))?;
        self.invoke(&path, None)
    }

    fn compile(&self, probe: &RepositoryProbe, lines: &[String]) -> Result<Run, String> {
        fs::write(&probe.source, format!("{}\n", lines.join("\n"))).map_err(|err| {
            format!(
                "trust audit: could not write {}: {err}",
                probe.source.display()
            )
        })?;
        self.invoke(&probe.source, Some(&probe.olean))
    }
}

impl Lean {
    fn invoke(&self, source: &Path, output: Option<&Path>) -> Result<Run, String> {
        let mut command = Command::new("lake");
        command.current_dir(&self.repository).args(["env", "lean"]);
        command.arg(source);
        if let Some(output) = output {
            command.arg("-o").arg(output);
        }
        let produced = command.output().map_err(|err| {
            format!(
                "trust audit: could not run `lake env lean`: {err}\nThis audit needs the pinned \
                 toolchain and must be run from the repository root."
            )
        })?;
        let mut lines: Vec<String> = Vec::new();
        for stream in [&produced.stdout, &produced.stderr] {
            for line in String::from_utf8_lossy(stream).lines() {
                lines.push(line.trim_end_matches('\r').to_string());
            }
        }
        Ok(Run {
            ok: produced.status.success(),
            lines,
        })
    }
}

// ---------------------------------------------------------------------------
// The probes.
// ---------------------------------------------------------------------------

/// The ten adversarial probes, in the order `audit-trust.ps1` ran them.
///
/// Each is named for the smuggling route it models. The two helpers below express
/// the only two shapes: "the audit must have refused this, saying <pattern>" and
/// "the audit must have accepted this, naming <pattern>".
struct Probes<'a, L: LeanDriver> {
    lean: &'a L,
    /// The nonce-named local command the aggregate audit is driven through, so the
    /// run is proved to have executed *this* audit rather than merely to have
    /// elaborated. Carried over from the original, including its reason: the public
    /// syntax spelling could be shadowed, the marker cannot.
    invocation: Vec<String>,
    marker: Regex,
}

/// The audit must have failed, and its output must name `pattern`.
///
/// Both halves matter. A probe that only checked the exit status would pass if the
/// audit failed for an unrelated reason -- a syntax error in the probe itself, most
/// obviously -- and would then be asserting nothing.
fn expect_refused(run: &Run, pattern: &Regex, failure: &str) -> Result<(), String> {
    if run.ok || !run.matches(pattern) {
        return Err(format!("{failure}\n{}", run.transcript()));
    }
    Ok(())
}

/// The audit must have succeeded, and its output must name `pattern`.
fn expect_named(run: &Run, pattern: &Regex, failure: &str) -> Result<(), String> {
    if !run.ok || !run.matches(pattern) {
        return Err(format!("{failure}\n{}", run.transcript()));
    }
    Ok(())
}

/// A case-insensitive line pattern, matching PowerShell's `-match`.
fn line_pattern(pattern: &str) -> Regex {
    Regex::new(&format!("(?i){pattern}")).expect("probe patterns are constants")
}

impl<'a, L: LeanDriver> Probes<'a, L> {
    fn new(lean: &'a L) -> Self {
        let nonce = nonce();
        let command = format!("grass_trust_audit_{nonce}");
        let marker = format!("grass-trust-audit-complete:{nonce}");
        Self {
            invocation: vec![
                "open Lean Elab Command".to_string(),
                format!("elab \"#{command}\" : command => do"),
                "  Grass.Trust.auditVerifiedPrograms".to_string(),
                format!("  logInfo \"{marker}\""),
                format!("#{command}"),
            ],
            marker: line_pattern(&regex::escape(&marker)),
            lean,
        }
    }

    /// The aggregate audit plus the `#print axioms` manifest.
    ///
    /// One file importing every library and non-entrypoint test module, so the audit
    /// sees the whole environment at once, followed by one `#print axioms` per named
    /// root.
    fn aggregate(&self, modules: &[String]) -> Result<usize, String> {
        let mut source: Vec<String> = modules.iter().map(|m| format!("import {m}")).collect();
        source.extend(self.invocation.iter().cloned());
        source.extend(DECLARATIONS.iter().map(|d| format!("#print axioms {d}")));
        let run = self.lean.elaborate(&source)?;
        if !run.ok {
            return Err(format!(
                "Lean could not audit the requested declaration closure.\n{}",
                run.transcript()
            ));
        }
        if !run.matches(&self.marker) {
            return Err(format!(
                "Lean did not execute the generated trust-audit driver.\n{}",
                run.transcript()
            ));
        }

        let no_axioms = Regex::new(NO_AXIOMS_PATTERN).expect("constant");
        let axioms = Regex::new(AXIOMS_PATTERN).expect("constant");
        let mut reported = 0;
        for line in &run.lines {
            match classify_axiom_line(&no_axioms, &axioms, line) {
                AxiomReport::None => reported += 1,
                AxiomReport::Depends(used) => {
                    reported += 1;
                    let rejected = rejected_axioms(&used, ALLOWED_AXIOMS);
                    if !rejected.is_empty() {
                        return Err(format!(
                            "Rejected transitive axiom(s): {}",
                            rejected.join(", ")
                        ));
                    }
                }
                AxiomReport::Other => println!("{line}"),
            }
        }
        if reported != DECLARATIONS.len() {
            return Err(format!(
                "Expected {} axiom reports, received {reported}.",
                DECLARATIONS.len()
            ));
        }
        Ok(reported)
    }

    /// Each executable test module, audited on its own.
    ///
    /// They all declare `main`, so importing two of them into one environment is
    /// impossible; this is the only place their closure is examined.
    fn entrypoints(&self, modules: &[String]) -> Result<(), String> {
        for module in modules {
            println!("Auditing executable test module '{module}'.");
            let mut source = vec![
                "import Tests.Foundation".to_string(),
                format!("import {module}"),
            ];
            source.extend(self.invocation.iter().cloned());
            let run = self.lean.elaborate(&source)?;
            if !run.ok || !run.matches(&self.marker) {
                return Err(format!(
                    "Trust audit failed for executable test module '{module}'.\n{}",
                    run.transcript()
                ));
            }
            for line in &run.lines {
                println!("{line}");
            }
        }
        Ok(())
    }

    /// A certificate pass-through is not a root.
    ///
    /// `def passthrough (verified : VerifiedProgram spec) : VerifiedProgram spec :=
    /// verified` has a `VerifiedProgram` result type and proves nothing: it is a
    /// function from a certificate to itself. If root discovery accepted it -- or
    /// accepted the constructor machinery Lean generates -- then every audit would
    /// find "roots" in any file and the emptiness check that guards the whole audit
    /// would never fire.
    fn root_nonvacuity(&self) -> Result<(), String> {
        let run = self.lean.elaborate(&[
            "import Grass.Trust.Audit".to_string(),
            "open Grass".to_string(),
            "def passthrough {spec : SpecProcess} (verified : VerifiedProgram spec) : VerifiedProgram spec := verified".to_string(),
            "#audit_verified_programs".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern("trust audit found no concrete VerifiedProgram declarations"),
            "Trust audit accepted generated constructor machinery or a certificate pass-through as a concrete root.",
        )
    }

    /// A root hidden behind an irreducible alias must still be discovered.
    ///
    /// `@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram spec`
    /// makes the result type opaque to ordinary unfolding. If the audit stopped at
    /// the alias, any certificate could be removed from its view by one type
    /// synonym.
    fn irreducible_discovery(&self) -> Result<(), String> {
        let run = self.lean.elaborate(&[
            "import Tests.Foundation".to_string(),
            "open Grass".to_string(),
            "@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram Grass.Tests.Foundation.spec".to_string(),
            "def cleanHiddenVerifiedProgram : HiddenVerifiedProgram := by".to_string(),
            "  unfold HiddenVerifiedProgram".to_string(),
            "  exact Grass.Tests.Foundation.verified".to_string(),
            "#audit_verified_programs".to_string(),
        ])?;
        expect_named(
            &run,
            &line_pattern("cleanHiddenVerifiedProgram"),
            "Trust audit did not discover a producer behind an irreducible result alias.",
        )
    }

    /// Authored underscore-prefixed roots in an *imported* module must be found.
    ///
    /// Lean generates internal declarations whose names begin with an underscore,
    /// and `_flat_ctor` in particular is a generated constructor name. An audit that
    /// skipped every such name to avoid its own generated noise would also skip a
    /// human-authored declaration deliberately given one of those names -- which is
    /// a two-line way to hide a certificate. All three spellings are checked, and
    /// from an imported `.olean` rather than the current file, because that is where
    /// the generated/authored distinction is hardest to make.
    fn imported_underscore_roots(&self, repository: &Path) -> Result<(), String> {
        let probe = RepositoryProbe::new(repository, "InternalRoot");
        let build = self.lean.compile(
            &probe,
            &[
                "import Tests.Foundation".to_string(),
                "open Grass".to_string(),
                "namespace InternalRootAuditProbe".to_string(),
                "@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram Grass.Tests.Foundation.spec".to_string(),
                "def _hiddenVerifiedProgram : HiddenVerifiedProgram := by".to_string(),
                "  unfold HiddenVerifiedProgram".to_string(),
                "  exact Grass.Tests.Foundation.verified".to_string(),
                "def _flat_ctor : HiddenVerifiedProgram := by".to_string(),
                "  unfold HiddenVerifiedProgram".to_string(),
                "  exact Grass.Tests.Foundation.verified".to_string(),
                "inductive AuthoredContainer where | node".to_string(),
                "def AuthoredContainer.node._flat_ctor : HiddenVerifiedProgram := by".to_string(),
                "  unfold HiddenVerifiedProgram".to_string(),
                "  exact Grass.Tests.Foundation.verified".to_string(),
                "end InternalRootAuditProbe".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the imported underscore-prefixed root probe.\n{}",
                build.transcript()
            ));
        }
        let run = self.lean.elaborate(&[
            format!("import {}", probe.module),
            "#audit_verified_programs".to_string(),
        ])?;
        for name in [
            r"InternalRootAuditProbe\._hiddenVerifiedProgram",
            r"InternalRootAuditProbe\._flat_ctor",
            r"InternalRootAuditProbe\.AuthoredContainer\.node\._flat_ctor",
        ] {
            expect_named(
                &run,
                &line_pattern(name),
                "Trust audit did not discover an imported authored underscore-prefixed root.",
            )?;
        }
        Ok(())
    }

    /// A certificate reached through `Classical.choice` of a `Nonempty` axiom.
    ///
    /// This is the central negative case: it is not a proof that a correct program
    /// exists, it is the *assumption* that one does, and the emitted bytes then
    /// carry no guarantee at all. `Nonempty` is the container; the audit has to see
    /// through it rather than only inspecting result types.
    fn wrapped_producer(&self) -> Result<(), String> {
        let run = self.lean.elaborate(&[
            "import Tests.Foundation".to_string(),
            "open Grass".to_string(),
            "namespace AuditProbe".to_string(),
            "axiom boxedVerifiedProgram : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)".to_string(),
            "noncomputable def emittedBytes : ByteArray := emitProgram (Classical.choice boxedVerifiedProgram)".to_string(),
            "end AuditProbe".to_string(),
            "#audit_verified_programs".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern("emittedBytes.*boxedVerifiedProgram"),
            "Trust audit did not reject a VerifiedProgram hidden in a container.",
        )
    }

    /// The same, under names that look generated.
    ///
    /// `_flat_ctor` again, this time on the *negative* side: a declaration a human
    /// wrote and named to look like Lean's own output must not be filtered out of
    /// the sensitive closure.
    fn user_declaration_named_like_generated(&self) -> Result<(), String> {
        let run = self.lean.elaborate(&[
            "import Tests.Foundation".to_string(),
            "open Grass".to_string(),
            "axiom AuditProbe.Source._flat_ctor : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)".to_string(),
            "noncomputable def AuditProbe.Sink._flat_ctor : ByteArray := emitProgram (Classical.choice AuditProbe.Source._flat_ctor)".to_string(),
            "#audit_verified_programs".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern("AuditProbe.Sink._flat_ctor.*AuditProbe.Source._flat_ctor"),
            "Trust audit ignored a user declaration named _flat_ctor.",
        )
    }

    /// An authored axiom whose name begins with an underscore.
    ///
    /// The same filter, applied to axioms rather than to roots. `Grass._unauditedFalse`
    /// is `False`; if it were skipped, everything downstream of it would be provable
    /// and audited clean.
    fn underscore_axiom(&self) -> Result<(), String> {
        let run = self.lean.elaborate(&[
            "import Tests.Foundation".to_string(),
            "axiom Grass._unauditedFalse : False".to_string(),
            "#audit_verified_programs".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern(r"Grass\._unauditedFalse.*rejected axioms"),
            "Trust audit ignored an authored underscore-prefixed axiom.",
        )
    }

    /// A wrapped producer in an arbitrarily named *imported* module.
    ///
    /// [`Probes::wrapped_producer`] with a module boundary in the way. The audit
    /// follows the dependency closure across imports rather than trusting the
    /// repository's namespace conventions, and this is what says so.
    fn wrapped_producer_from_import(&self, repository: &Path) -> Result<(), String> {
        let probe = RepositoryProbe::new(repository, "External");
        let build = self.lean.compile(
            &probe,
            &[
                "import Tests.Foundation".to_string(),
                "open Grass".to_string(),
                "namespace ExternalAuditProbe".to_string(),
                "axiom boxedVerifiedProgram : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)".to_string(),
                "noncomputable def emittedBytes : ByteArray := emitProgram (Classical.choice boxedVerifiedProgram)".to_string(),
                "end ExternalAuditProbe".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the imported external trust-audit probe.\n{}",
                build.transcript()
            ));
        }
        let run = self.lean.elaborate(&[
            format!("import {}", probe.module),
            "#audit_verified_programs".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern(
                "ExternalAuditProbe.emittedBytes.*ExternalAuditProbe.boxedVerifiedProgram",
            ),
            "Trust audit ignored a wrapped producer from an imported external module.",
        )
    }

    /// `@[implemented_by]` in the runtime closure downstream of emission.
    ///
    /// The proved definition is the identity on bytes; the compiled one returns an
    /// empty `ByteArray`. Every theorem about the emitted program still holds, and
    /// the artefact a user runs is empty. No axiom, no warning, no `unsafe` marker
    /// -- nothing else in the repository can see this.
    fn implemented_by_replacement(&self, repository: &Path) -> Result<(), String> {
        let probe = RepositoryProbe::new(repository, "Runtime");
        let build = self.lean.compile(
            &probe,
            &[
                "namespace ExternalRuntimeAuditProbe".to_string(),
                "unsafe def replacement (_ : ByteArray) : ByteArray := ByteArray.empty".to_string(),
                "@[implemented_by replacement]".to_string(),
                "def identityBytes (bytes : ByteArray) : ByteArray := bytes".to_string(),
                "end ExternalRuntimeAuditProbe".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the implemented_by trust-audit probe.\n{}",
                build.transcript()
            ));
        }
        let run = self.lean.elaborate(&[
            format!("import {}", probe.module),
            "import Tests.Foundation".to_string(),
            "open Grass".to_string(),
            "def ExternalRuntimeAuditProbe.emittedBytes".to_string(),
            "    (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :="
                .to_string(),
            "  ExternalRuntimeAuditProbe.identityBytes (emitProgram verified)".to_string(),
            "#audit_runtime_dependencies ExternalRuntimeAuditProbe.emittedBytes".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern("ExternalRuntimeAuditProbe.identityBytes.*implemented_by.*ExternalRuntimeAuditProbe.replacement"),
            "Trust audit ignored an implemented_by replacement in the runtime dependency closure.",
        )
    }

    /// `@[extern]` reached through an ordinarily imported module.
    ///
    /// The same severance, effected by native code instead of by another Lean
    /// definition, and reached through two module boundaries rather than one: the
    /// probe module carries the attribute, a second compiled module consumes it, and
    /// the audit runs against that second module. A closure that only looked at the
    /// file in front of it would see neither.
    fn extern_replacement(&self, repository: &Path) -> Result<(), String> {
        let probe = RepositoryProbe::new(repository, "Extern");
        let build = self.lean.compile(
            &probe,
            &[
                "namespace ExternalRuntimeAuditProbe".to_string(),
                "@[extern \"grass_runtime_probe_identity\"]".to_string(),
                "def identityBytes (bytes : ByteArray) : ByteArray := bytes".to_string(),
                "end ExternalRuntimeAuditProbe".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the extern trust-audit probe.\n{}",
                build.transcript()
            ));
        }
        let consumer = RepositoryProbe::new(repository, "ExternConsumer");
        let build = self.lean.compile(
            &consumer,
            &[
                format!("import {}", probe.module),
                "import Tests.Foundation".to_string(),
                "open Grass".to_string(),
                "def ExternalRuntimeAuditConsumer.emittedBytes".to_string(),
                "    (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :="
                    .to_string(),
                "  emitProgram verified".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the extern importing-module trust-audit probe.\n{}",
                build.transcript()
            ));
        }
        let run = self.lean.elaborate(&[
            format!("import {}", consumer.module),
            "#audit_runtime_dependencies ExternalRuntimeAuditConsumer.emittedBytes".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern("ExternalRuntimeAuditProbe.identityBytes.*extern"),
            "Trust audit ignored an extern implementation in an ordinarily imported runtime module.",
        )
    }

    /// A `csimp` substitution whose `local` attribute has already expired.
    ///
    /// The hardest of the ten. `attribute [local csimp]` rewrites the compiled code
    /// of the consumer module and is then gone: by the time the audit runs against
    /// the imported result, there is no attribute in the environment to find. The
    /// audit has to reach the replacement through participating module cohorts and
    /// persisted non-meta compiler dependency modules instead, which is what the
    /// three-module arrangement below is for -- source module, replacement module,
    /// and a consumer compiled with the local attribute in scope.
    fn expired_scoped_csimp(&self, repository: &Path) -> Result<(), String> {
        let source = RepositoryProbe::new(repository, "CsimpSource");
        let build = self.lean.compile(
            &source,
            &[
                "namespace ExternalRuntimeAuditSource".to_string(),
                "def identityBytes (bytes : ByteArray) : ByteArray := bytes".to_string(),
                "end ExternalRuntimeAuditSource".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the scoped-csimp source probe.\n{}",
                build.transcript()
            ));
        }
        let replacement = RepositoryProbe::new(repository, "Csimp");
        let build = self.lean.compile(
            &replacement,
            &[
                format!("import {}", source.module),
                "namespace ExternalScopedCSimpProbe".to_string(),
                "unsafe def runtimeReplacement (_ : ByteArray) : ByteArray := ByteArray.empty".to_string(),
                "@[implemented_by runtimeReplacement]".to_string(),
                "def replacement (bytes : ByteArray) : ByteArray := bytes".to_string(),
                "theorem replacement_eq : ExternalRuntimeAuditSource.identityBytes = replacement := rfl".to_string(),
                "end ExternalScopedCSimpProbe".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the scoped-csimp replacement probe.\n{}",
                build.transcript()
            ));
        }
        let consumer = RepositoryProbe::new(repository, "CsimpConsumer");
        let build = self.lean.compile(
            &consumer,
            &[
                format!("import {}", source.module),
                format!("import {}", replacement.module),
                "import Tests.Foundation".to_string(),
                "open Grass".to_string(),
                "section".to_string(),
                "attribute [local csimp] ExternalScopedCSimpProbe.replacement_eq".to_string(),
                "def ExternalScopedCSimpProbe.emittedBytes".to_string(),
                "    (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :="
                    .to_string(),
                "  ExternalRuntimeAuditSource.identityBytes (emitProgram verified)".to_string(),
                "end".to_string(),
            ],
        )?;
        if !build.ok {
            return Err(format!(
                "Could not compile the imported scoped-csimp consumer probe.\n{}",
                build.transcript()
            ));
        }
        let run = self.lean.elaborate(&[
            format!("import {}", consumer.module),
            "#audit_runtime_dependencies ExternalScopedCSimpProbe.emittedBytes".to_string(),
        ])?;
        expect_refused(
            &run,
            &line_pattern(
                "ExternalScopedCSimpProbe.(replacement.*implemented_by.*runtimeReplacement|runtimeReplacement.*unsafe)",
            ),
            "Trust audit ignored a scoped csimp replacement after its attribute state expired.",
        )
    }
}

// ---------------------------------------------------------------------------
// Running it.
// ---------------------------------------------------------------------------

/// The whole audit, over an injected Lean driver.
///
/// The ten probes run in the order `audit-trust.ps1` ran them. Six of them pass
/// only when the elaboration they drove *failed*, and the last thing this function
/// does before returning `Ok` is one of those six. Every one of those statuses is
/// consumed into this `Result` and nowhere else; see [`exit_status`].
fn audit<L: LeanDriver>(lean: &L, repository: &Path, scan: &Scan) -> Result<String, String> {
    verdict(scan)?;

    let probes = Probes::new(lean);

    let reported = probes.aggregate(&scan.aggregate())?;
    probes.entrypoints(&scan.entrypoint)?;

    probes.root_nonvacuity()?;
    probes.irreducible_discovery()?;
    probes.imported_underscore_roots(repository)?;
    probes.wrapped_producer()?;
    probes.user_declaration_named_like_generated()?;
    probes.underscore_axiom()?;
    probes.wrapped_producer_from_import(repository)?;
    probes.implemented_by_replacement(repository)?;
    probes.extern_replacement(repository)?;
    probes.expired_scoped_csimp(repository)?;

    Ok(passing_line(reported, scan.entrypoint.len()))
}

fn run() -> Result<String, String> {
    let repository = std::env::current_dir()
        .map_err(|err| format!("trust audit: could not read the working directory: {err}"))?;
    let scan = scan_sources(&repository)?;
    let lean = Lean::new(&repository)?;
    audit(&lean, &repository, &scan)
}

/// The process exit status a finished audit deserves: 0 for a pass, 1 for
/// anything else.
///
/// This is one line and it has a test, which is disproportionate until you know
/// what it replaces. `audit-trust.ps1` never called `exit`, and GitHub's
/// `shell: pwsh` wrapper exits with `$LASTEXITCODE` -- the status of the last
/// native command the script ran. On the *success* path that command was the
/// scoped-csimp probe's `lake env lean`, which the audit requires to fail: the
/// check reads `if ($LASTEXITCODE -eq 0 ...) { throw }`. Passing the audit
/// therefore guaranteed a non-zero exit. The gate failed all 39 of its last 39
/// runs while printing "Trust audit passed ..." as its final line, and a gate that
/// always fails hides a regression exactly as well as one that always passes.
///
/// The shape of that bug was that the exit status was a *side effect* of the last
/// thing that happened rather than a statement about the verdict. Here it is a
/// total function of the verdict and nothing else, and it is derived from a value
/// no child process can write to.
fn exit_status(result: &Result<String, String>) -> u8 {
    match result {
        Ok(_) => 0,
        Err(_) => 1,
    }
}

fn main() -> ExitCode {
    let result = run();
    match &result {
        Ok(message) => println!("{message}"),
        Err(message) => eprintln!("{message}"),
    }
    ExitCode::from(exit_status(&result))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scan_of(library: &[&str], test: &[&str], entrypoint: &[&str]) -> Scan {
        Scan {
            library: library.iter().map(|m| (*m).to_string()).collect(),
            test: test.iter().map(|m| (*m).to_string()).collect(),
            entrypoint: entrypoint.iter().map(|m| (*m).to_string()).collect(),
        }
    }

    fn classify(line: &str) -> AxiomReport {
        classify_axiom_line(
            &Regex::new(NO_AXIOMS_PATTERN).expect("constant"),
            &Regex::new(AXIOMS_PATTERN).expect("constant"),
            line,
        )
    }

    // --- the vacuous-pass refusals ---------------------------------------

    #[test]
    fn an_audit_with_no_executable_test_modules_is_refused() {
        // The failure this port exists to close. `audit-trust.ps1` printed
        // "Trust audit passed for 58 declaration(s) and 0 executable test
        // module(s)." and exited 0.
        let message = verdict(&scan_of(&["Grass.A"], &["Tests.Foundation"], &[]))
            .expect_err("auditing no executable test module must not report success");
        assert!(
            message.contains("not one executable entrypoint"),
            "{message}"
        );
        assert!(
            message.contains("Refusing to report \"0 executable test module(s)\" as a pass"),
            "{message}"
        );
        assert!(
            !message.contains("Trust audit passed"),
            "an empty scan must never borrow the success line: {message}"
        );
    }

    #[test]
    fn an_empty_library_root_is_refused() {
        let message = verdict(&scan_of(&[], &["Tests.Foundation"], &["Tests.Main"]))
            .expect_err("no library module must not report success");
        assert!(message.contains("contain no Lean modules"), "{message}");
        assert!(message.contains("Grass"), "{message}");
    }

    #[test]
    fn an_empty_test_root_is_refused_before_the_entrypoint_message() {
        // Distinct from the case above: there are no test modules at all, so
        // "found 0 test modules and not one entrypoint" would misdescribe it.
        let message = verdict(&scan_of(&["Grass.A"], &[], &[]))
            .expect_err("no test module must not report success");
        assert!(
            message.contains("test source root(s) Tests contain no Lean modules"),
            "{message}"
        );
    }

    #[test]
    fn a_populated_scan_passes_the_emptiness_checks() {
        assert!(verdict(&scan_of(
            &["Grass.A"],
            &["Tests.Foundation"],
            &["Tests.Main"]
        ))
        .is_ok());
    }

    #[test]
    fn the_declaration_manifest_is_the_reviewed_one() {
        // The original's `if ($Declaration.Count -eq 0) { throw }` was a runtime
        // check because the list arrived from the command line. It is a constant
        // here, so the same guarantee is a test rather than a branch nothing can
        // take. The count is asserted so that removing a root is a visible change,
        // and uniqueness because a repeated name would inflate the expected report
        // count without auditing anything more.
        assert_eq!(DECLARATIONS.len(), 57);
        let unique: std::collections::BTreeSet<&str> = DECLARATIONS.iter().copied().collect();
        assert_eq!(unique.len(), DECLARATIONS.len());
    }

    // --- the axiom judgement ----------------------------------------------

    #[test]
    fn the_allowlist_comparison_is_ordinal() {
        // The original ran this on every invocation because PowerShell's
        // case-sensitive operators are culture-sensitive. Here it is a property of
        // the language, asserted once. A case variant is a different axiom.
        let used = vec!["Propext".to_string()];
        assert_eq!(rejected_axioms(&used, ALLOWED_AXIOMS), vec!["Propext"]);
        let allowed = vec!["propext".to_string()];
        assert!(rejected_axioms(&allowed, ALLOWED_AXIOMS).is_empty());
    }

    #[test]
    fn only_the_three_reviewed_constants_are_permitted() {
        let used: Vec<String> = ["propext", "Classical.choice", "Quot.sound"]
            .iter()
            .map(|a| (*a).to_string())
            .collect();
        assert!(rejected_axioms(&used, ALLOWED_AXIOMS).is_empty());

        let used = vec![
            "propext".to_string(),
            "sorryAx".to_string(),
            "Grass.someDependencyAxiom".to_string(),
        ];
        assert_eq!(
            rejected_axioms(&used, ALLOWED_AXIOMS),
            vec!["sorryAx", "Grass.someDependencyAxiom"]
        );
    }

    #[test]
    fn print_axioms_output_is_read_the_way_lean_writes_it() {
        assert_eq!(
            classify("'Grass.emitProgram_parses' does not depend on any axioms"),
            AxiomReport::None
        );
        assert_eq!(
            classify("'Grass.VerifiedProgram.sound' depends on axioms: [propext, Quot.sound]"),
            AxiomReport::Depends(vec!["propext".to_string(), "Quot.sound".to_string()])
        );
        // Anything else is a diagnostic, not a report, and is passed through.
        assert_eq!(classify("info: building Grass"), AxiomReport::Other);
        assert_eq!(classify(""), AxiomReport::Other);
        // Not anchored loosely: a report has to be the whole line.
        assert_eq!(
            classify("note: 'X' does not depend on any axioms today"),
            AxiomReport::Other
        );
    }

    // --- the module partition ---------------------------------------------

    #[test]
    fn a_source_path_becomes_the_module_it_declares() {
        assert_eq!(
            module_name("Grass/ISA/X86/Decode.lean"),
            "Grass.ISA.X86.Decode"
        );
        assert_eq!(module_name("Tests/Foundation.lean"), "Tests.Foundation");
        assert_eq!(module_name("Grass\\Trust\\Audit.lean"), "Grass.Trust.Audit");
    }

    #[test]
    fn a_top_level_main_makes_a_test_module_an_entrypoint() {
        let main = Regex::new(TOP_LEVEL_MAIN_PATTERN).expect("constant");
        assert!(main.is_match("def main : IO Unit := pure ()"));
        assert!(main.is_match("import X\n\ndef main : IO Unit := pure ()\n"));
        assert!(main.is_match("unsafe def main : IO Unit := pure ()"));
        assert!(main.is_match("partial def main (args : List String) : IO Unit := pure ()"));
        assert!(main.is_match("noncomputable def main: IO Unit := pure ()"));
        // Indented is still top level as far as this pattern is concerned; the
        // original's comment argues a false positive only costs an extra pass.
        assert!(main.is_match("  def main : IO Unit := pure ()"));
        // A nested or differently named runner is not one.
        assert!(!main.is_match("def mainLoop : IO Unit := pure ()"));
        assert!(!main.is_match("theorem main_spec : True := trivial"));
        assert!(!main.is_match("  let main := 1"));
    }

    #[test]
    fn the_aggregate_is_sorted_and_deduplicated() {
        let scan = scan_of(
            &["Grass.B", "Grass.A"],
            &["Tests.Foundation", "Grass.A"],
            &["Tests.Main"],
        );
        assert_eq!(
            scan.aggregate(),
            vec![
                "Grass.A".to_string(),
                "Grass.B".to_string(),
                "Tests.Foundation".to_string()
            ]
        );
        assert!(
            !scan.aggregate().contains(&"Tests.Main".to_string()),
            "an entrypoint module must never enter the aggregate import"
        );
    }

    #[test]
    fn the_scan_partitions_a_tree_by_whether_a_module_declares_main() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Grass/Trust")).expect("mkdir");
        fs::create_dir_all(root.join("Tests/ISA")).expect("mkdir");
        fs::write(root.join("Grass/Certificate.lean"), "def f := 1").expect("write");
        fs::write(root.join("Grass/Trust/Audit.lean"), "def g := 1").expect("write");
        fs::write(root.join("Grass/notes.md"), "not Lean").expect("write");
        fs::write(root.join("Tests/Foundation.lean"), "def spec := 1").expect("write");
        fs::write(
            root.join("Tests/ISA/NasmCorpus.lean"),
            "import Tests.Foundation\n\ndef main : IO Unit := pure ()\n",
        )
        .expect("write");

        let scan = scan_sources(root).expect("scan");
        assert_eq!(
            scan.library,
            vec![
                "Grass.Certificate".to_string(),
                "Grass.Trust.Audit".to_string()
            ]
        );
        assert_eq!(scan.test, vec!["Tests.Foundation".to_string()]);
        assert_eq!(scan.entrypoint, vec!["Tests.ISA.NasmCorpus".to_string()]);
        assert!(verdict(&scan).is_ok());
    }

    #[test]
    fn an_empty_tree_scans_to_nothing_and_is_then_refused() {
        // The other half of the falsification: the walk really does return nothing,
        // so `verdict` really does meet the empty cases above.
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Grass")).expect("mkdir");
        fs::create_dir_all(root.join("Tests")).expect("mkdir");
        let scan = scan_sources(root).expect("scan");
        assert_eq!(scan, Scan::default());
        assert!(verdict(&scan).is_err());
    }

    #[test]
    fn a_test_tree_with_no_entrypoint_scans_and_is_then_refused() {
        // The exact vacuous pass: the library is whole, the tests are present, and
        // not one of them declares `main`.
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        fs::create_dir_all(root.join("Grass")).expect("mkdir");
        fs::create_dir_all(root.join("Tests")).expect("mkdir");
        fs::write(root.join("Grass/Certificate.lean"), "def f := 1").expect("write");
        fs::write(root.join("Tests/Foundation.lean"), "def spec := 1").expect("write");
        let scan = scan_sources(root).expect("scan");
        assert!(scan.entrypoint.is_empty());
        assert!(verdict(&scan).is_err());
    }

    #[test]
    fn a_missing_source_root_is_named() {
        let dir = tempfile::tempdir().expect("tempdir");
        let message = scan_sources(dir.path()).expect_err("a missing root must be an error");
        assert!(
            message.contains("configured source root 'Grass' does not exist"),
            "{message}"
        );
    }

    // --- the probe expectations -------------------------------------------

    fn run_of(ok: bool, lines: &[&str]) -> Run {
        Run {
            ok,
            lines: lines.iter().map(|l| (*l).to_string()).collect(),
        }
    }

    #[test]
    fn a_probe_that_must_be_refused_needs_both_a_failure_and_the_reason() {
        let pattern = line_pattern("emittedBytes.*boxedVerifiedProgram");
        let refused = run_of(
            false,
            &["error: certificate-sensitive declaration 'AuditProbe.emittedBytes' uses rejected axioms: [AuditProbe.boxedVerifiedProgram]"],
        );
        assert!(expect_refused(&refused, &pattern, "x").is_ok());

        // The audit accepted it: the smuggling route is open.
        let accepted = run_of(true, &["trust audit passed"]);
        assert!(expect_refused(&accepted, &pattern, "x").is_err());

        // The case that decides whether this function reads the exit status at
        // all: the audit named the very thing the probe is about -- so the
        // pattern matches -- and then exited 0. That is a *worse* result than
        // silence, because the audit saw the smuggled certificate, said so, and
        // passed anyway; a check that only looked for the names would call it a
        // success. Dropping `run.ok` from the condition above leaves every other
        // case in this test green.
        let named_but_passed = run_of(
            true,
            &["note: AuditProbe.emittedBytes mentions AuditProbe.boxedVerifiedProgram"],
        );
        assert!(
            expect_refused(&named_but_passed, &pattern, "x").is_err(),
            "an audit that named the route and still exited 0 has not refused anything"
        );

        // It failed, but for an unrelated reason -- a syntax error in the probe,
        // say. That is not evidence the audit noticed anything.
        let unrelated = run_of(false, &["error: unknown identifier 'emitProgram'"]);
        let message = expect_refused(&unrelated, &pattern, "the probe's own message")
            .expect_err("an unrelated failure must not satisfy a probe");
        assert!(message.starts_with("the probe's own message"), "{message}");
        assert!(
            message.contains("unknown identifier"),
            "the diagnostics travel with the finding: {message}"
        );
    }

    #[test]
    fn a_probe_that_must_be_discovered_needs_both_a_pass_and_the_name() {
        let pattern = line_pattern("cleanHiddenVerifiedProgram");
        assert!(expect_named(
            &run_of(true, &["... roots: [cleanHiddenVerifiedProgram]"]),
            &pattern,
            "x"
        )
        .is_ok());
        // Passed without finding it: root discovery has gone blind.
        assert!(expect_named(&run_of(true, &["... roots: []"]), &pattern, "x").is_err());
        assert!(expect_named(
            &run_of(false, &["... cleanHiddenVerifiedProgram ..."]),
            &pattern,
            "x"
        )
        .is_err());
    }

    #[test]
    fn line_matching_is_per_line_and_case_insensitive() {
        // `$output -match $pattern` over an array asks whether *some element*
        // matches, so a pattern spanning two lines of one Lean message never
        // matched, and `-match` ignores case. Both preserved.
        let run = run_of(false, &["AuditProbe.Sink", "AuditProbe.Source"]);
        assert!(!run.matches(&line_pattern("Sink.*Source")));
        assert!(run.matches(&line_pattern("auditprobe.sink")));
    }

    #[test]
    fn the_passing_line_is_the_sentence_the_original_printed() {
        assert_eq!(
            passing_line(57, 6),
            "Trust audit passed for 57 declaration(s) and 6 executable test module(s)."
        );
    }

    #[test]
    fn a_nonce_does_not_repeat_within_a_run() {
        let names: std::collections::BTreeSet<String> = (0..64).map(|_| nonce()).collect();
        assert_eq!(names.len(), 64);
    }

    #[test]
    fn a_repository_probe_removes_both_of_its_files() {
        let dir = tempfile::tempdir().expect("tempdir");
        fs::create_dir_all(dir.path().join(".lake/build/lib/lean")).expect("mkdir");
        let (source, olean) = {
            let probe = RepositoryProbe::new(dir.path(), "Test");
            fs::write(&probe.source, "def f := 1").expect("write");
            fs::write(&probe.olean, "").expect("write");
            assert!(probe.module.starts_with("GrassToolsTrustAuditTest"));
            (probe.source.clone(), probe.olean.clone())
        };
        assert!(!source.exists(), "the generated source outlived its probe");
        assert!(!olean.exists(), "the generated olean outlived its probe");
    }

    // --- the exit status of the success path -------------------------------
    //
    // This is the bug `audit-trust.ps1` shipped, and it is the reason these tests
    // assert on a *status* rather than on the passing sentence. The script printed
    // "Trust audit passed for 57 declaration(s) and 6 executable test module(s)."
    // and exited non-zero, every run, for 39 runs. A test that read the message
    // would have been green throughout.

    /// A stand-in for `lake env lean` that answers from a script.
    ///
    /// It is not a stub returning constants: for the two things the audit reads out
    /// of Lean's output rather than out of its exit status, it behaves the way Lean
    /// does. It echoes the audit's own generated marker back, because `logInfo` in
    /// the generated driver is what puts it on stdout; and it answers every
    /// `#print axioms X` with the line `#print axioms` writes. That means the
    /// script below carries only what each probe is *about* -- whether the
    /// elaboration succeeded, and what it named -- rather than a transcript nobody
    /// could check.
    struct ScriptedLean {
        responses: std::cell::RefCell<std::collections::VecDeque<(bool, Vec<String>)>>,
        /// The `ok` flag of every run served, in order, so a test can ask what the
        /// last invocation did.
        served: std::cell::RefCell<Vec<bool>>,
    }

    impl ScriptedLean {
        fn new(responses: Vec<(bool, Vec<String>)>) -> Self {
            Self {
                responses: std::cell::RefCell::new(responses.into()),
                served: std::cell::RefCell::new(Vec::new()),
            }
        }

        fn next(&self, extra: Vec<String>) -> Run {
            let (ok, scripted) = self
                .responses
                .borrow_mut()
                .pop_front()
                .expect("the audit asked Lean for more than the script provides");
            self.served.borrow_mut().push(ok);
            let mut lines = extra;
            lines.extend(scripted);
            Run { ok, lines }
        }

        fn exhausted(&self) -> bool {
            self.responses.borrow().is_empty()
        }

        fn last_run_failed(&self) -> bool {
            self.served.borrow().last().copied() == Some(false)
        }

        fn runs_served(&self) -> usize {
            self.served.borrow().len()
        }
    }

    impl LeanDriver for ScriptedLean {
        fn elaborate(&self, lines: &[String]) -> Result<Run, String> {
            let mut echoed = Vec::new();
            for line in lines {
                // `logInfo "<marker>"` in the generated driver reaches stdout.
                if let Some(marker) = line.trim().strip_prefix("logInfo \"") {
                    echoed.push(marker.trim_end_matches('"').to_string());
                }
                // `#print axioms X` reports on X.
                if let Some(name) = line.strip_prefix("#print axioms ") {
                    echoed.push(format!("'{name}' does not depend on any axioms"));
                }
            }
            Ok(self.next(echoed))
        }

        fn compile(&self, _probe: &RepositoryProbe, _lines: &[String]) -> Result<Run, String> {
            Ok(self.next(Vec::new()))
        }
    }

    /// The exact sequence of Lean invocations a passing audit makes, in order.
    ///
    /// Six of the ten probes pass *because* the elaboration failed; those carry
    /// `false`. The three probes that need an imported module compile it first, and
    /// a compile must succeed for its probe to mean anything. Read the `false`
    /// entries as "this probe's whole point is that Lean rejected it".
    fn a_passing_script(entrypoints: usize) -> Vec<(bool, Vec<String>)> {
        let mut script = vec![
            // aggregate: the marker and the 57 reports are synthesised by the fake.
            (true, vec![]),
        ];
        // entrypoints: one elaboration each, marker synthesised.
        script.extend((0..entrypoints).map(|_| (true, vec![])));
        script.extend([
            // root_nonvacuity -- must be refused.
            (
                false,
                vec!["trust audit found no concrete VerifiedProgram declarations".to_string()],
            ),
            // irreducible_discovery -- must succeed and name the producer.
            (
                true,
                vec!["found root cleanHiddenVerifiedProgram".to_string()],
            ),
            // imported_underscore_roots: compile, then an audit naming all three.
            (true, vec![]),
            (
                true,
                vec![
                    "root InternalRootAuditProbe._hiddenVerifiedProgram".to_string(),
                    "root InternalRootAuditProbe._flat_ctor".to_string(),
                    "root InternalRootAuditProbe.AuthoredContainer.node._flat_ctor".to_string(),
                ],
            ),
            // wrapped_producer -- must be refused.
            (
                false,
                vec![
                    "AuditProbe.emittedBytes depends on AuditProbe.boxedVerifiedProgram"
                        .to_string(),
                ],
            ),
            // user_declaration_named_like_generated -- must be refused.
            (
                false,
                vec![
                    "AuditProbe.Sink._flat_ctor depends on AuditProbe.Source._flat_ctor"
                        .to_string(),
                ],
            ),
            // underscore_axiom -- must be refused.
            (
                false,
                vec!["Grass._unauditedFalse is among the rejected axioms".to_string()],
            ),
            // wrapped_producer_from_import: compile, then a refusal.
            (true, vec![]),
            (
                false,
                vec!["ExternalAuditProbe.emittedBytes depends on \
                     ExternalAuditProbe.boxedVerifiedProgram"
                    .to_string()],
            ),
            // implemented_by_replacement: compile, then a refusal.
            (true, vec![]),
            (
                false,
                vec![
                    "ExternalRuntimeAuditProbe.identityBytes has implemented_by \
                     ExternalRuntimeAuditProbe.replacement"
                        .to_string(),
                ],
            ),
            // extern_replacement: two compiles, then a refusal.
            (true, vec![]),
            (true, vec![]),
            (
                false,
                vec!["ExternalRuntimeAuditProbe.identityBytes is extern".to_string()],
            ),
            // expired_scoped_csimp: three compiles, then the final refusal. This is
            // the last Lean invocation of the whole run, and it exits non-zero.
            (true, vec![]),
            (true, vec![]),
            (true, vec![]),
            (
                false,
                vec!["ExternalScopedCSimpProbe.replacement has implemented_by \
                     ExternalScopedCSimpProbe.runtimeReplacement"
                    .to_string()],
            ),
        ]);
        script
    }

    fn a_populated_scan() -> Scan {
        Scan {
            library: vec!["Grass".to_string(), "Grass.Trust.Audit".to_string()],
            test: vec!["Tests.Foundation".to_string()],
            entrypoint: vec!["Tests.Std.Text".to_string(), "Tests.Std.Vec".to_string()],
        }
    }

    #[test]
    fn the_success_path_exits_zero_though_its_last_lean_invocation_failed() {
        // The falsification of `audit-trust.ps1`'s defect, in the one form that
        // would have caught it: drive every probe to its *passing* outcome, note
        // that the last thing Lean did was fail, and assert on the exit status.
        let scan = a_populated_scan();
        let lean = ScriptedLean::new(a_passing_script(scan.entrypoint.len()));
        let repository = tempfile::tempdir().expect("tempdir");

        let result = audit(&lean, repository.path(), &scan);

        assert!(
            result.is_ok(),
            "every probe was driven to its passing outcome: {result:?}"
        );
        assert_eq!(
            result.as_deref(),
            Ok("Trust audit passed for 57 declaration(s) and 2 executable test module(s)."),
            "the 57 `#print axioms` reports were all counted"
        );
        assert!(
            lean.exhausted(),
            "the audit made fewer Lean invocations than the script describes, so some probe \
             did not run"
        );
        assert!(
            lean.last_run_failed(),
            "the premise of this test: the final `lake env lean` of a passing run exits \
             non-zero, which is what made the PowerShell fail while passing"
        );
        assert_eq!(
            exit_status(&result),
            0,
            "a passing audit must exit 0, no matter what the last child process returned"
        );
    }

    #[test]
    fn a_declaration_that_stops_reporting_fails_the_audit() {
        // The manifest is stated rather than discovered precisely so that a
        // refactor which stops a theorem being reachable fails the gate instead
        // of quietly shrinking it. Lean prints nothing for a `#print axioms` it
        // could not resolve beyond a diagnostic, which `classify_axiom_line`
        // reads as `Other` and passes through -- so the count is the only thing
        // that notices. Without it, an audit of 56 of the 57 roots reports the
        // same clean line as an audit of all of them.
        struct OneShort;
        impl LeanDriver for OneShort {
            fn elaborate(&self, lines: &[String]) -> Result<Run, String> {
                let mut out = Vec::new();
                let mut skipped = false;
                for line in lines {
                    if let Some(marker) = line.trim().strip_prefix("logInfo \"") {
                        out.push(marker.trim_end_matches('"').to_string());
                    }
                    if let Some(name) = line.strip_prefix("#print axioms ") {
                        if !skipped {
                            // The first root elaborates to a diagnostic instead
                            // of a report, as a name that no longer exists does.
                            skipped = true;
                            out.push(format!("unknown identifier '{name}'"));
                            continue;
                        }
                        out.push(format!("'{name}' does not depend on any axioms"));
                    }
                }
                Ok(Run {
                    ok: true,
                    lines: out,
                })
            }

            fn compile(&self, _probe: &RepositoryProbe, _lines: &[String]) -> Result<Run, String> {
                Ok(Run {
                    ok: true,
                    lines: Vec::new(),
                })
            }
        }

        let result = audit(&OneShort, Path::new("."), &a_populated_scan());
        let message = result
            .as_ref()
            .expect_err("56 reports for 57 roots is not a complete audit");
        assert_eq!(message, "Expected 57 axiom reports, received 56.");
        assert_eq!(exit_status(&result), 1);
    }

    #[test]
    fn a_failing_probe_exits_non_zero() {
        // The other half: the status must actually distinguish the two verdicts. A
        // gate that always exits 0 is as useless as one that always exits 1.
        let scan = a_populated_scan();
        let mut script = a_passing_script(scan.entrypoint.len());
        // Make the last probe -- the scoped-csimp one -- succeed, which is the
        // failure it is there to detect.
        let last = script.len() - 1;
        script[last] = (true, vec!["nothing to report".to_string()]);
        let lean = ScriptedLean::new(script);
        let repository = tempfile::tempdir().expect("tempdir");

        let result = audit(&lean, repository.path(), &scan);

        let message = result.as_ref().expect_err("the probe must have failed");
        assert!(
            message.contains("scoped csimp replacement after its attribute state expired"),
            "{message}"
        );
        assert_eq!(exit_status(&result), 1);
    }

    #[test]
    fn an_empty_scan_is_refused_before_lean_is_asked_anything() {
        // The emptiness refusal must come first, or a run over the wrong tree
        // spends fifteen elaborations discovering it has nothing to audit.
        let lean = ScriptedLean::new(Vec::new());
        let repository = tempfile::tempdir().expect("tempdir");

        let result = audit(&lean, repository.path(), &Scan::default());

        assert_eq!(lean.runs_served(), 0, "Lean was invoked over an empty scan");
        assert!(result
            .as_ref()
            .expect_err("an empty scan is not a clean audit")
            .contains("contain no Lean modules"));
        assert_eq!(exit_status(&result), 1);
    }

    #[test]
    fn the_exit_status_is_a_function_of_the_verdict_alone() {
        assert_eq!(exit_status(&Ok("Trust audit passed for 57".to_string())), 0);
        assert_eq!(exit_status(&Err("Rejected axiom sorryAx".to_string())), 1);
    }
}
