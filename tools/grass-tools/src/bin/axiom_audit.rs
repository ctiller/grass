//! Enforce the trust boundary in `docs/FOUNDATION.md` section 3.
//!
//! > Every theorem used by the verified gate is audited transitively for axioms,
//! > regardless of which dependency declared them. Only the reviewed Lean logical
//! > foundation allowlist (`propext`, quotient soundness, and classical choice, with
//! > their exact toolchain declaration names) is permitted. Dependency-defined
//! > axioms, `sorryAx`, `sorry`, `admit`, unsafe declarations used as proof, and
//! > equivalent admission mechanisms make the gate fail.
//!
//! Three things fail the gate, and they are checked in this order because the first
//! is the one a reader is least likely to expect:
//!
//! 1. a compiled override -- `@[implemented_by]` or `@[extern]` -- on a `Grass`
//!    declaration, which lets the definition a differential executes differ from the
//!    definition a theorem is about;
//! 2. an `unsafe` declaration in the `Grass` namespace;
//! 3. a dependency on any axiom outside [`ALLOWED_AXIOMS`].
//!
//! Exit status is 1 if any of the three fires.
//!
//! # What is Rust here and what cannot be
//!
//! Which axioms a declaration depends on is not a property of its source text. It is
//! the kernel's record of the proof term it checked, transitively through every
//! constant that proof mentions, and nothing outside a Lean environment can read it.
//! A textual approximation would be the worst possible outcome for this particular
//! gate: it is the repository's central trust boundary, and a checker that guesses
//! reports green for reasons unrelated to whether the tree is sound.
//!
//! So the kernel stays the oracle and the policy moves here. The generated
//! meta-program in [`audit_lean_source`] reports facts and judges nothing: for each
//! declaration in the `Grass` namespace it writes out the axioms the kernel recorded,
//! whether the declaration is `unsafe`, and which compiled override it carries, if
//! any. Everything that decides -- the allowlist, what counts as a finding, the
//! precedence between the three failures, the messages and the exit status -- is in
//! this file, where it is unit-testable without a six-minute Lean build.
//!
//! One judgement stays on the Lean side, deliberately: the `Grass`-namespace filter.
//! `collectAxioms` is the expensive part of the run, and applying it to core Lean's
//! declarations before discarding them here would multiply a 22-second audit by the
//! size of the toolchain. [`is_audited`] reimplements the predicate anyway and
//! [`judge`] applies it to every record the snippet sends, so the snippet narrowing
//! the set wrongly is a loud failure rather than a quiet under-report.
//!
//! # Where the import list comes from
//!
//! It used to be written by hand, at the top of the Lean file this replaces, and that
//! file's own comment records how that went: "within a day of being written it had
//! fallen six modules behind the tree, and a maximally false axiom in an unimported
//! module passed both this tool and `lake build` with exit 0."
//!
//! The fix there was a coverage check. The fix here is that there is no list to fall
//! behind: [`module_names`] walks `Grass/` and the walk's result *is* the import
//! list. Lean still has no dynamic import, so a list is still generated -- into a
//! temporary file that `lake env lean` elaborates under the pinned toolchain, never
//! into a tracked one that `main` and a branch can disagree about.
//!
//! That disagreement is the second reason this port exists. A hand-written registry
//! of every module in the tree is edited by every change that adds a module, so a
//! branch deleting it conflicts with `main` on every rebase and can never converge.
//! `Tools/AxiomAudit.lean` and `Tools/DeclNames.lean` were the two files with that
//! shape, and they blocked the nine-binary port for that reason rather than for any
//! defect in it.
//!
//! ## The coverage check is kept anyway
//!
//! Generating the imports from the tree walk makes the list unable to *fall behind*.
//! It does not make the walk correct. A generator that skipped a directory, or that
//! mapped a file name to the wrong module, would produce a list that is complete with
//! respect to itself and short with respect to the tree -- which is the original
//! failure wearing new clothes.
//!
//! So the snippet reports `env.header.moduleNames` back, and [`judge`] fails if a
//! module the walk found is absent from it. Lean's own tree walk is gone but Lean's
//! own record of what it imported is not, and that record is what the walk is checked
//! against. The two implementations are independent, which is the property that
//! matters.
//!
//! # One deliberate departure
//!
//! An audit tool that finds nothing to audit and reports success is the failure mode
//! this repository has already been bitten by, and the Lean original had it. Its
//! coverage check compares the disk against the imports, so an empty `Grass/` makes
//! the comparison vacuous rather than loud: the hand-written imports still resolve
//! against whatever `.olean` files are on `LEAN_PATH`, the audit still runs against
//! them, and it reports on a tree it never looked at.
//!
//! Measured, not reasoned about. Against a directory holding `lakefile.toml`, an
//! empty `Grass/`, and the built library on `LEAN_PATH`, the original printed
//!
//! ```text
//! axiom audit: 13790 Grass declarations across 0 modules, no axiom outside the
//! allowlist, no unsafe declaration, no compiled override
//! ```
//!
//! and exited 0. "Across 0 modules" is the whole diagnosis, in a line whose every
//! other word says the tree is clean.
//!
//! [`run`] refuses that. Here the import list *is* the tree walk, so no modules on
//! disk means nothing would be audited at all; finding none is a failure, reported as
//! one, naming the directory it looked in -- and reported *before* the Lean run, so
//! the diagnosis arrives in a second rather than after an elaboration that was never
//! going to say anything.
//!
//! # Two differences that are not departures
//!
//! Findings are sorted. The original iterated `env.constants.toList`, whose order is
//! a hash map's, so two runs over the same tree could report the same findings in
//! different orders and a reviewer diffing two reports would see churn. Sorting is
//! what makes the report a value.
//!
//! The original's messages reached the terminal through `throwError` and `logInfo`,
//! so Lean prefixed each with the source position inside `Tools/AxiomAudit.lean`.
//! There is no such file now and the prefix is gone. The lines themselves -- the
//! summary, and the `  {name} depends on {axiom}` findings under it -- are the
//! original's, unchanged, which is what makes the two runs comparable.
//!
//! # A limit inherited on purpose
//!
//! The original's prose named `@[implemented_by]`, `@[extern]` and `@[csimp]` as
//! "exactly the three ways" to separate a compiled definition from its logical one,
//! and then checked two of them. This port checks the same two. Closing the gap means
//! deciding what a `@[csimp]` lemma proved *about* the definition it replaces implies
//! for the differentials, which is a question for the reviewer of a change that adds
//! one, not something to settle silently inside a port whose purpose is to be
//! behaviourally identical. It is written down here so it is a known limit rather
//! than an assumed absence.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::{Command, ExitCode};

/// The reviewed logical-foundation allowlist.
///
/// Exactly the three constants `docs/FOUNDATION.md` section 3 permits, by their
/// toolchain declaration names. Adding to this list is a trust-boundary change and
/// requires the review that section demands, not an edit here.
const ALLOWED_AXIOMS: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

/// The namespace the audit covers.
const AUDITED_NAMESPACE: &str = "Grass";

/// The directory walked to produce the import list, relative to the repository root.
const LIBRARY_ROOT: &str = "Grass";

/// The name a declaration is written under, with any `private` mangling removed.
///
/// A `private` declaration is stored as `_private.<module>.<n>.<real name>`, whose
/// first component is `_private` rather than `Grass`. Testing the namespace on the
/// stored name skipped every private declaration in the library -- 111 in the x86
/// tree alone, including proof-carrying theorems -- which is the defect the Lean
/// original's `userFacing` was added to fix.
///
/// Lean's `privateToUserName?` strips the first three components. This does the same,
/// and returns the name unchanged when it is not mangled.
fn user_facing(name: &str) -> &str {
    let Some(rest) = name.strip_prefix("_private.") else {
        return name;
    };
    // `_private.<module path>.<n>.<real name>`: the counter is the last purely
    // numeric component before the real name, so scan for it rather than counting
    // dots, which a dotted module path makes meaningless.
    let mut search = rest;
    let mut consumed = "_private.".len();
    while let Some(dot) = search.find('.') {
        let (component, after) = search.split_at(dot);
        let after = &after[1..];
        consumed += dot + 1;
        if !component.is_empty() && component.chars().all(|c| c.is_ascii_digit()) {
            return &name[consumed..];
        }
        search = after;
    }
    name
}

/// Whether a declaration belongs to the audited namespace.
///
/// The prefix test is on components, not on characters: `Grasshopper.foo` starts with
/// the string `Grass` and is not in the `Grass` namespace.
fn is_audited(name: &str) -> bool {
    let name = user_facing(name);
    name == AUDITED_NAMESPACE
        || name
            .strip_prefix(AUDITED_NAMESPACE)
            .is_some_and(|rest| rest.starts_with('.'))
}

/// Whether a module name can be written after `import` without quoting.
///
/// Generating an import list means a file name reaches the elaborator as syntax.
/// Every module in this tree is `UpperCamelCase`, but a file named `x-y.lean` would
/// produce a parse error inside a generated file the reader never sees, and the
/// diagnosis would be a puzzle. Refusing it by name is the self-healing version of
/// that failure.
fn is_plain_module_name(name: &str) -> bool {
    !name.is_empty()
        && name.split('.').all(|part| {
            let mut chars = part.chars();
            matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
        })
}

/// A Lean string literal for `text`, so a Windows path survives being pasted into
/// generated source.
fn lean_string_literal(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

/// The generated meta-program: a fact dump, with the import list filled in from disk
/// and the record set written where the caller asked.
///
/// It judges nothing. `collectAxioms` is the kernel's record and the only part of
/// this that cannot be done here; the allowlist it used to be compared against lives
/// in [`ALLOWED_AXIOMS`] now.
///
/// The `Grass._authoredUnderscoreProbe` guard is the Lean original's, kept in place.
/// It fires at elaboration time if the namespace filter ever stops seeing an authored
/// declaration whose name begins with an underscore -- the shape that `isInternal`,
/// the obvious way to write this filter, would silently drop.
fn audit_lean_source(modules: &[String], out: &Path) -> String {
    let imports = modules
        .iter()
        .map(|m| format!("import {m}\n"))
        .collect::<String>();
    let out_literal = lean_string_literal(&out.to_string_lossy());
    format!(
        r#"import Lean
{imports}
open Lean

run_cmd do
  let probe := (privateToUserName? `Grass._authoredUnderscoreProbe).getD `Grass._authoredUnderscoreProbe
  unless (`Grass).isPrefixOf probe do
    throwError "axiom audit would skip an authored underscore-prefixed Grass declaration"

run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  let mut lines : Array String := #[]
  for m in env.header.moduleNames do
    lines := lines.push ("M\t" ++ toString m)
  let mut decls : Nat := 0
  let mut deps : Nat := 0
  for (name, info) in env.constants.toList do
    let user := (privateToUserName? name).getD name
    unless (`Grass).isPrefixOf user do continue
    decls := decls + 1
    lines := lines.push ("C\t" ++ toString name)
    if info.isUnsafe then
      lines := lines.push ("U\t" ++ toString name)
    if (Lean.Compiler.getImplementedBy? env name).isSome then
      lines := lines.push ("O\t@[implemented_by]\t" ++ toString user)
    else if Lean.isExtern env name then
      lines := lines.push ("O\t@[extern]\t" ++ toString user)
    let axioms ← Elab.Command.liftCoreM (collectAxioms name)
    for used in axioms do
      deps := deps + 1
      lines := lines.push ("A\t" ++ toString used ++ "\t" ++ toString name)
  lines := lines.push ("Z\t" ++ toString decls ++ "\t" ++ toString deps)
  IO.FS.writeFile {out_literal} (String.intercalate "\n" lines.toList ++ "\n")
"#
    )
}

/// The facts the generated snippet reports, parsed.
#[derive(Debug, Default, PartialEq, Eq)]
struct Facts {
    /// Every module the elaborated environment imported, transitively.
    imported: BTreeSet<String>,
    /// Every declaration the snippet audited, by its stored name.
    declarations: BTreeSet<String>,
    /// The audited declarations that are `unsafe`, by stored name.
    unsafe_declarations: BTreeSet<String>,
    /// Audited declarations carrying a compiled override, by user-facing name.
    overrides: BTreeMap<String, String>,
    /// Stored declaration name to the axioms the kernel recorded for it.
    axioms: BTreeMap<String, BTreeSet<String>>,
}

/// Parse the tab-separated record set the generated snippet writes.
///
/// Six record kinds, one per line: `M` an imported module, `C` an audited
/// declaration, `U` an audited `unsafe` declaration, `O` a compiled override and the
/// attribute spelling, `A` a declaration's dependency on one axiom, and `Z` the
/// terminator carrying the `C` and `A` counts.
///
/// The terminator is the point of the format. A Lean process killed part-way through,
/// or a disk that filled, would otherwise hand back a shorter record set that parses
/// perfectly -- and a short record set is a *clean* audit, because every finding this
/// tool can make requires a record to be present. Truncation is exactly the failure
/// that must not read as success here.
///
/// Fields are counted rather than split off the front, so a name containing a tab
/// produces a record with the wrong arity and is refused by name instead of quietly
/// shifting the meaning of a column.
fn parse_audit_records(text: &str) -> Result<Facts, String> {
    let mut facts = Facts::default();
    let mut terminator: Option<(usize, usize)> = None;
    let mut dependency_records = 0usize;

    for (index, line) in text.lines().enumerate() {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() {
            continue;
        }
        let number = index + 1;
        if terminator.is_some() {
            return Err(format!(
                "axiom audit records: record {number} follows the terminator: {line:?}"
            ));
        }
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["M", module] => {
                facts.imported.insert((*module).to_string());
            }
            ["C", name] => {
                facts.declarations.insert((*name).to_string());
            }
            ["U", name] => {
                facts.unsafe_declarations.insert((*name).to_string());
            }
            ["O", attr, name] => {
                facts
                    .overrides
                    .insert((*name).to_string(), (*attr).to_string());
            }
            ["A", used, name] => {
                dependency_records += 1;
                facts
                    .axioms
                    .entry((*name).to_string())
                    .or_default()
                    .insert((*used).to_string());
            }
            ["Z", decls, deps] => {
                let decls = decls.parse::<usize>().map_err(|err| {
                    format!("axiom audit records: record {number} has an unreadable count: {err}")
                })?;
                let deps = deps.parse::<usize>().map_err(|err| {
                    format!("axiom audit records: record {number} has an unreadable count: {err}")
                })?;
                terminator = Some((decls, deps));
            }
            _ => {
                return Err(format!(
                    "axiom audit records: record {number} is not a record this tool wrote: {line:?}"
                ))
            }
        }
    }

    let Some((decls, deps)) = terminator else {
        return Err(
            "axiom audit records: the record set has no terminator, so it describes some \
                    of the audited declarations rather than all of them. Refusing to report a \
                    clean audit against a partial record set."
                .to_string(),
        );
    };
    if decls != facts.declarations.len() {
        return Err(format!(
            "axiom audit records: the record set claims {decls} audited declarations and carries \
             {}, so it was truncated in transit.",
            facts.declarations.len()
        ));
    }
    if deps != dependency_records {
        return Err(format!(
            "axiom audit records: the record set claims {deps} axiom dependencies and carries \
             {dependency_records}, so it was truncated in transit."
        ));
    }
    Ok(facts)
}

/// Elaborate the generated snippet under the repository's toolchain and read the
/// records back.
///
/// `lake env lean` is how `.github/workflows/library.yml` invoked the Lean original,
/// and it is what puts the built `.olean` files on `LEAN_PATH`; the working directory
/// therefore has to be the repository root, exactly as it did before.
///
/// A missing or failing oracle is an error, not a skip. An axiom audit that passes
/// because it could not reach the kernel is worse than no axiom audit.
///
/// The record set goes to a file rather than to standard output so a Lean diagnostic
/// can never be mistaken for a fact.
fn run_audit_snippet(modules: &[String]) -> Result<String, String> {
    let dir = tempfile::Builder::new()
        .prefix("grass-axiom-audit")
        .tempdir()
        .map_err(|err| format!("could not run the axiom audit: {err}"))?;
    let script = dir.path().join("AxiomAuditProbe.lean");
    let records = dir.path().join("records.tsv");
    fs::write(&script, audit_lean_source(modules, &records))
        .map_err(|err| format!("could not run the axiom audit: {err}"))?;

    let output = Command::new("lake")
        .args(["env", "lean"])
        .arg(&script)
        .output()
        .map_err(|err| format!("could not run the axiom audit:\n{err}"))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    if !output.status.success() {
        let combined = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
        let capped: String = combined.trim().chars().take(4000).collect();
        return Err(format!("could not run the axiom audit:\n{capped}"));
    }
    fs::read_to_string(&records).map_err(|err| {
        let capped: String = stdout.trim().chars().take(4000).collect();
        format!("could not run the axiom audit ({err}):\n{capped}")
    })
}

/// The dotted module name of every `.lean` file under `root`.
///
/// The same walk that produces this list is the only thing that produces it, so there
/// is nothing for it to fall out of step with. What it is checked against is Lean's
/// own report of what it imported; see [`judge`].
fn module_names(root: &Path, prefix: &str) -> Result<Vec<String>, String> {
    let mut modules = Vec::new();
    let mut stack = vec![(root.to_path_buf(), prefix.to_string())];
    while let Some((dir, dotted)) = stack.pop() {
        let entries = match fs::read_dir(&dir) {
            Ok(entries) => entries,
            // A missing root is not an error here: it is the empty walk, which
            // `run` turns into a refusal that names the directory.
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => continue,
            Err(err) => return Err(format!("{}: {err}", dir.display())),
        };
        for entry in entries {
            let entry = entry.map_err(|err| format!("{}: {err}", dir.display()))?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let file_type = entry
                .file_type()
                .map_err(|err| format!("{}: {err}", entry.path().display()))?;
            if file_type.is_dir() {
                stack.push((entry.path(), format!("{dotted}.{name}")));
            } else if let Some(stem) = name.strip_suffix(".lean") {
                modules.push(format!("{dotted}.{stem}"));
            }
        }
    }
    modules.sort();
    modules.dedup();
    Ok(modules)
}

/// What the audit concluded.
#[derive(Debug)]
struct Report {
    /// The report's lines, in the order they are printed.
    lines: Vec<String>,
    /// Whether any of the three failures fired.
    failed: bool,
}

/// Apply `docs/FOUNDATION.md` section 3 to the facts the kernel reported.
///
/// The three failures are checked in the Lean original's order and the first one that
/// fires is the whole report, because they are not independent: an `@[implemented_by]`
/// declaration's axioms are about a term nothing executes, so listing them under a
/// compiled-override failure would be noise.
///
/// `walked` is the module list the import list was generated from. It is checked
/// against `facts.imported` here rather than in the snippet, so that the check is
/// made by code that did not produce the list being checked.
fn judge(facts: &Facts, walked: &[String]) -> Result<Report, String> {
    let missing: Vec<&String> = walked
        .iter()
        .filter(|m| !facts.imported.contains(*m))
        .collect();
    if !missing.is_empty() {
        let mut message = String::from(
            "axiom audit coverage gap: these modules exist under Grass/ but are absent from the \
             environment the audit ran against, so their declarations were never scanned:\n",
        );
        for module in missing {
            let _ = writeln!(message, "  {module}");
        }
        return Err(message.trim_end().to_string());
    }

    // The snippet narrows to the `Grass` namespace for speed; this is the check that
    // it narrowed to the right set. A stray declaration here means the filter in the
    // generated source and `is_audited` disagree, and the audit's scope is not what
    // this file says it is.
    if let Some(stray) = facts.declarations.iter().find(|name| !is_audited(name)) {
        return Err(format!(
            "axiom audit: the environment reported {stray}, which is not in the {AUDITED_NAMESPACE} \
             namespace. The generated filter and `is_audited` disagree about what is audited; \
             refusing to report against a scope this tool cannot describe."
        ));
    }

    if !facts.overrides.is_empty() {
        let mut lines = vec![
            "axiom audit failed: a Grass declaration's compiled behaviour is allowed to differ \
             from its logical definition. Every differential in this repository measures the \
             compiled definition while every theorem is about the logical one, so this severs \
             the two."
                .to_string(),
        ];
        for (name, attr) in &facts.overrides {
            lines.push(format!("  {name} carries {attr}"));
        }
        return Ok(Report {
            lines,
            failed: true,
        });
    }

    if !facts.unsafe_declarations.is_empty() {
        let mut lines = vec![
            "axiom audit failed; docs/FOUNDATION.md section 3 forbids unsafe \
                              declarations used as proof:"
                .to_string(),
        ];
        for name in &facts.unsafe_declarations {
            lines.push(format!("  {name}"));
        }
        return Ok(Report {
            lines,
            failed: true,
        });
    }

    // Ordered by declaration, then by axiom, because [`Facts`] holds both in
    // `BTree` collections. A `sort` here would be dead code -- it was written, and a
    // mutation run found that removing it changed nothing -- and dead code that looks
    // like a guarantee is the shape this repository keeps getting caught by. The
    // guarantee is the container's; `report_is_ordered_by_declaration_then_axiom`
    // pins it against enough names that an unordered one could not pass.
    let mut findings: Vec<String> = Vec::new();
    for (name, used) in &facts.axioms {
        for axiom in used {
            if !ALLOWED_AXIOMS.contains(&axiom.as_str()) {
                findings.push(format!("  {name} depends on {axiom}"));
            }
        }
    }
    if !findings.is_empty() {
        let mut lines = vec![format!(
            "axiom audit failed; docs/FOUNDATION.md section 3 permits only [{}]",
            ALLOWED_AXIOMS.join(", ")
        )];
        lines.extend(findings);
        return Ok(Report {
            lines,
            failed: true,
        });
    }

    Ok(Report {
        lines: vec![format!(
            "axiom audit: {} Grass declarations across {} modules, no axiom outside the \
             allowlist, no unsafe declaration, no compiled override",
            facts.declarations.len(),
            walked.len()
        )],
        failed: false,
    })
}

/// The message behind this port's one deliberate departure from the Lean original.
///
/// A tree-walking auditor run from the wrong directory finds nothing, imports
/// nothing, audits nothing, and exits 0, which is indistinguishable from a clean
/// tree. Naming the working directory is what turns the failure into a diagnosis.
fn zero_modules_message(root: &str) -> String {
    let cwd = std::env::current_dir()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|err| format!("<unavailable: {err}>"));
    format!(
        "axiom audit: found no .lean files under {root}/ from {cwd}, so it audited nothing.\n\
         Refusing to report a clean audit of an empty scan: run this from the repository root."
    )
}

fn run() -> Result<ExitCode, String> {
    // The module list is gathered before Lean is invoked. A wrong working directory
    // breaks both, and "found no modules" is the diagnosis; reaching it first also
    // means the failure does not wait on a full elaboration to arrive.
    let modules = module_names(Path::new(LIBRARY_ROOT), AUDITED_NAMESPACE)?;
    if modules.is_empty() {
        return Err(zero_modules_message(LIBRARY_ROOT));
    }
    if let Some(bad) = modules.iter().find(|m| !is_plain_module_name(m)) {
        return Err(format!(
            "could not run the axiom audit: {bad} is not a module name that can be imported \
             without quoting. Rename the file, or teach `audit_lean_source` to quote."
        ));
    }

    let records = run_audit_snippet(&modules)?;
    let facts = parse_audit_records(&records)?;
    let report = judge(&facts, &modules)?;

    if report.failed {
        for line in &report.lines {
            eprintln!("{line}");
        }
        return Ok(ExitCode::FAILURE);
    }
    for line in &report.lines {
        println!("{line}");
    }
    Ok(ExitCode::SUCCESS)
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn facts_from(text: &str) -> Facts {
        parse_audit_records(text).expect("records should parse")
    }

    /// The record set a clean single-declaration tree produces.
    fn clean_records() -> String {
        "M\tGrass.Core.Name\nC\tGrass.Core.Name.foo\nA\tpropext\tGrass.Core.Name.foo\nZ\t1\t1\n"
            .to_string()
    }

    #[test]
    fn a_clean_record_set_reports_the_counts_and_succeeds() {
        let facts = facts_from(&clean_records());
        let report = judge(&facts, &["Grass.Core.Name".to_string()]).unwrap();
        assert!(!report.failed);
        assert_eq!(
            report.lines,
            vec![
                "axiom audit: 1 Grass declarations across 1 modules, no axiom outside the \
                 allowlist, no unsafe declaration, no compiled override"
            ]
        );
    }

    #[test]
    fn every_allowlisted_axiom_is_accepted() {
        let mut text = String::from("M\tGrass.A\nC\tGrass.A.t\n");
        for axiom in ALLOWED_AXIOMS {
            let _ = writeln!(text, "A\t{axiom}\tGrass.A.t");
        }
        let _ = writeln!(text, "Z\t1\t{}", ALLOWED_AXIOMS.len());
        let facts = facts_from(&text);
        assert!(!judge(&facts, &["Grass.A".to_string()]).unwrap().failed);
    }

    #[test]
    fn sorry_is_a_finding() {
        let facts = facts_from(
            "M\tGrass.A\nC\tGrass.A.t\nA\tsorryAx\tGrass.A.t\nA\tpropext\tGrass.A.t\nZ\t1\t2\n",
        );
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert!(report.failed);
        assert_eq!(
            report.lines,
            vec![
                "axiom audit failed; docs/FOUNDATION.md section 3 permits only [propext, \
                 Classical.choice, Quot.sound]",
                "  Grass.A.t depends on sorryAx",
            ]
        );
    }

    #[test]
    fn a_dependency_declared_axiom_is_a_finding() {
        let facts =
            facts_from("M\tGrass.A\nC\tGrass.A.t\nA\tMathlib.someAxiom\tGrass.A.t\nZ\t1\t1\n");
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert!(report.failed);
        assert!(report.lines[1].ends_with("depends on Mathlib.someAxiom"));
    }

    #[test]
    fn findings_are_sorted_so_two_runs_produce_the_same_report() {
        let facts = facts_from(
            "M\tGrass.A\nC\tGrass.A.z\nC\tGrass.A.a\nA\tsorryAx\tGrass.A.z\n\
             A\tsorryAx\tGrass.A.a\nZ\t2\t2\n",
        );
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert_eq!(
            &report.lines[1..],
            [
                "  Grass.A.a depends on sorryAx",
                "  Grass.A.z depends on sorryAx",
            ]
        );
    }

    /// The ordering guarantee, pinned at a size an unordered container could not
    /// pass by luck.
    ///
    /// The Lean original iterated `env.constants.toList` -- a hash map's order -- so
    /// two runs over one tree could report the same findings in different orders and
    /// a reviewer diffing two reports saw churn that meant nothing. Two names do not
    /// distinguish an ordered container from an unordered one; sixty do.
    #[test]
    fn report_is_ordered_by_declaration_then_axiom() {
        let mut text = String::from("M\tGrass.A\n");
        let mut expected: Vec<String> = Vec::new();
        // Fed in descending order, so insertion order is the reverse of the answer.
        for i in (0..30).rev() {
            let name = format!("Grass.A.d{i:02}");
            let _ = writeln!(text, "C\t{name}");
            for axiom in ["zzzAxiom", "aaaAxiom"] {
                let _ = writeln!(text, "A\t{axiom}\t{name}");
                expected.push(format!("  {name} depends on {axiom}"));
            }
        }
        let _ = writeln!(text, "Z\t30\t60");
        expected.sort();

        let facts = facts_from(&text);
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert!(report.failed);
        assert_eq!(&report.lines[1..], expected.as_slice());
    }

    #[test]
    fn an_unsafe_declaration_is_a_finding() {
        let facts = facts_from("M\tGrass.A\nC\tGrass.A.t\nU\tGrass.A.t\nZ\t1\t0\n");
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert!(report.failed);
        assert_eq!(
            report.lines,
            vec![
                "axiom audit failed; docs/FOUNDATION.md section 3 forbids unsafe declarations \
                 used as proof:",
                "  Grass.A.t",
            ]
        );
    }

    #[test]
    fn a_compiled_override_is_a_finding_and_outranks_the_others() {
        // Both an override and a forbidden axiom are present. The override is the
        // whole report: the axioms of a declaration nothing executes are noise.
        let facts = facts_from(
            "M\tGrass.A\nC\tGrass.A.t\nU\tGrass.A.t\nO\t@[implemented_by]\tGrass.A.t\n\
             A\tsorryAx\tGrass.A.t\nZ\t1\t1\n",
        );
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert!(report.failed);
        assert_eq!(report.lines.len(), 2);
        assert_eq!(report.lines[1], "  Grass.A.t carries @[implemented_by]");
    }

    #[test]
    fn an_extern_override_is_reported_by_its_own_spelling() {
        let facts = facts_from("M\tGrass.A\nC\tGrass.A.t\nO\t@[extern]\tGrass.A.t\nZ\t1\t0\n");
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert_eq!(report.lines[1], "  Grass.A.t carries @[extern]");
    }

    #[test]
    fn an_unsafe_declaration_outranks_an_axiom_finding() {
        let facts =
            facts_from("M\tGrass.A\nC\tGrass.A.t\nU\tGrass.A.t\nA\tsorryAx\tGrass.A.t\nZ\t1\t1\n");
        let report = judge(&facts, &["Grass.A".to_string()]).unwrap();
        assert_eq!(report.lines.len(), 2);
        assert_eq!(report.lines[1], "  Grass.A.t");
    }

    #[test]
    fn a_module_on_disk_that_the_environment_never_imported_is_a_coverage_gap() {
        let facts = facts_from(&clean_records());
        let err = judge(
            &facts,
            &["Grass.Core.Name".to_string(), "Grass.Core.Uid".to_string()],
        )
        .unwrap_err();
        assert!(err.contains("coverage gap"), "{err}");
        assert!(err.contains("Grass.Core.Uid"), "{err}");
        assert!(!err.contains("Grass.Core.Name"), "{err}");
    }

    #[test]
    fn a_declaration_outside_the_namespace_is_refused_rather_than_audited() {
        let facts = facts_from("M\tGrass.A\nC\tList.map\nZ\t1\t0\n");
        let err = judge(&facts, &["Grass.A".to_string()]).unwrap_err();
        assert!(err.contains("List.map"), "{err}");
        assert!(err.contains("disagree"), "{err}");
    }

    #[test]
    fn a_truncated_record_set_is_refused_rather_than_reported_clean() {
        // Every finding needs a record, so a truncated set is a *clean* audit.
        let err = parse_audit_records("M\tGrass.A\nC\tGrass.A.t\nZ\t2\t0\n").unwrap_err();
        assert!(err.contains("truncated"), "{err}");
    }

    #[test]
    fn a_record_set_with_a_short_dependency_count_is_refused() {
        let err = parse_audit_records("M\tGrass.A\nC\tGrass.A.t\nA\tpropext\tGrass.A.t\nZ\t1\t9\n")
            .unwrap_err();
        assert!(err.contains("axiom dependencies"), "{err}");
    }

    #[test]
    fn a_record_set_with_no_terminator_is_refused() {
        let err = parse_audit_records("M\tGrass.A\nC\tGrass.A.t\n").unwrap_err();
        assert!(err.contains("no terminator"), "{err}");
    }

    #[test]
    fn a_record_after_the_terminator_is_refused() {
        let err = parse_audit_records("C\tGrass.A.t\nZ\t1\t0\nC\tGrass.A.u\n").unwrap_err();
        assert!(err.contains("follows the terminator"), "{err}");
    }

    #[test]
    fn an_unrecognised_record_is_refused() {
        let err = parse_audit_records("X\tsomething\nZ\t0\t0\n").unwrap_err();
        assert!(err.contains("not a record this tool wrote"), "{err}");
    }

    #[test]
    fn a_name_carrying_a_tab_is_refused_rather_than_shifting_a_column() {
        // `A` takes exactly three fields; a fourth means a name contained a tab and
        // the axiom column would otherwise have silently become part of a name.
        let err = parse_audit_records("A\tpropext\tGrass.A\tt\nZ\t0\t1\n").unwrap_err();
        assert!(err.contains("not a record this tool wrote"), "{err}");
    }

    #[test]
    fn private_mangling_is_stripped_so_a_private_theorem_is_audited() {
        assert_eq!(
            user_facing("_private.Grass.ISA.X86.Decode.0.Grass.ISA.X86.decode_sound"),
            "Grass.ISA.X86.decode_sound"
        );
        assert!(is_audited(
            "_private.Grass.ISA.X86.Decode.0.Grass.ISA.X86.decode_sound"
        ));
    }

    #[test]
    fn an_unmangled_name_is_returned_unchanged() {
        assert_eq!(user_facing("Grass.Core.Name.foo"), "Grass.Core.Name.foo");
        assert_eq!(user_facing("_private"), "_private");
        assert_eq!(
            user_facing("_private.NoCounter.here"),
            "_private.NoCounter.here"
        );
    }

    /// The Lean original carried this as a `run_cmd` guard, because `isInternal` --
    /// the obvious way to write the namespace filter -- drops it.
    #[test]
    fn an_authored_underscore_prefixed_declaration_is_still_audited() {
        assert!(is_audited("Grass._authoredUnderscoreProbe"));
    }

    #[test]
    fn the_namespace_test_is_on_components_and_not_on_characters() {
        assert!(is_audited("Grass"));
        assert!(is_audited("Grass.Core.Name"));
        assert!(!is_audited("Grasshopper.foo"));
        assert!(!is_audited("GrassX"));
        assert!(!is_audited("List.map"));
        assert!(!is_audited("NotGrass.Grass.foo"));
    }

    #[test]
    fn the_module_walk_finds_every_lean_file_at_any_depth_in_sorted_order() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join("Grass");
        fs::create_dir_all(root.join("ISA/X86")).unwrap();
        fs::create_dir_all(root.join("Core")).unwrap();
        fs::write(root.join("Process.lean"), "").unwrap();
        fs::write(root.join("Core/Name.lean"), "").unwrap();
        fs::write(root.join("ISA/X86/Decode.lean"), "").unwrap();
        // Not a Lean source: must not become a module.
        fs::write(root.join("Core/notes.md"), "").unwrap();
        assert_eq!(
            module_names(&root, "Grass").unwrap(),
            vec![
                "Grass.Core.Name".to_string(),
                "Grass.ISA.X86.Decode".to_string(),
                "Grass.Process".to_string(),
            ]
        );
    }

    #[test]
    fn a_missing_root_walks_to_nothing_rather_than_erroring() {
        let dir = tempfile::tempdir().unwrap();
        assert!(module_names(&dir.path().join("absent"), "Grass")
            .unwrap()
            .is_empty());
    }

    /// The failure this port exists to make impossible: an empty scan reading as a
    /// clean tree. The message has to name the directory, or the diagnosis is a
    /// puzzle rather than an instruction.
    #[test]
    fn scanning_no_modules_is_a_loud_failure_naming_the_directory() {
        let message = zero_modules_message("Grass");
        assert!(message.contains("audited nothing"), "{message}");
        assert!(message.contains("Grass/"), "{message}");
        assert!(message.contains("repository root"), "{message}");
    }

    #[test]
    fn the_generated_snippet_imports_every_module_the_walk_found() {
        let modules = vec!["Grass.Core.Name".to_string(), "Grass.Process".to_string()];
        let source = audit_lean_source(&modules, Path::new("records.tsv"));
        for module in &modules {
            assert!(source.contains(&format!("import {module}\n")), "{source}");
        }
        // The kernel's record, not a re-derivation of it.
        assert!(source.contains("collectAxioms"), "{source}");
        // No judgement in the snippet beyond the namespace narrowing.
        assert!(!source.contains("propext"), "{source}");
    }

    #[test]
    fn a_module_name_needing_quotes_is_refused_by_name() {
        assert!(is_plain_module_name("Grass.ISA.X86.Decode"));
        assert!(is_plain_module_name("Grass.Std.Logical.Vec'"));
        assert!(!is_plain_module_name("Grass.x-y"));
        assert!(!is_plain_module_name("Grass.9Lives"));
        assert!(!is_plain_module_name(""));
    }

    #[test]
    fn a_windows_path_survives_becoming_a_lean_literal() {
        assert_eq!(
            lean_string_literal(r"C:\Temp\records.tsv"),
            r#""C:\\Temp\\records.tsv""#
        );
        assert_eq!(lean_string_literal(r#"a"b"#), r#""a\"b""#);
    }

    #[test]
    fn the_snippet_writes_its_records_to_the_path_it_was_given() {
        let source = audit_lean_source(&["Grass.A".to_string()], Path::new(r"C:\Temp\r.tsv"));
        assert!(
            source.contains(r#"IO.FS.writeFile "C:\\Temp\\r.tsv""#),
            "{source}"
        );
    }
}
