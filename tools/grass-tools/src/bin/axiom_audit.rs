//! Audit every `Grass` declaration for the axioms it depends on.
//!
//! `docs/FOUNDATION.md` §3: "Every theorem used by the verified gate is audited
//! transitively for axioms, regardless of which dependency declared them. Only the
//! reviewed Lean logical foundation allowlist (`propext`, quotient soundness, and
//! classical choice, with their exact toolchain declaration names) is permitted.
//! Dependency-defined axioms, `sorryAx`, `sorry`, `admit`, unsafe declarations used
//! as proof, and equivalent admission mechanisms make the gate fail."
//!
//! This tool implements that audit over every declaration in the `Grass` namespace.
//! It is run by `.github/workflows/library.yml` and fails the build on any axiom
//! outside the allowlist.
//!
//! It is also not a proof. `docs/FOUNDATION.md` §3 is discharged by the kernel
//! recording which axioms each declaration depends on; this tool reads that record
//! and reports. A green run is evidence, in the sense of `docs/VALIDATION.md`, not
//! a theorem.
//!
//! # Why a Rust program that writes Lean
//!
//! The kernel's axiom record lives in the Lean environment and nowhere else, so
//! some part of this has to be a Lean meta-program. What does *not* have to be
//! Lean is the judgement: which axioms are allowed, what counts as coverage, what
//! the verdict is, and whether the run examined enough to mean anything. Those
//! moved here, where they are unit-tested without a six-second elaboration.
//!
//! The Lean that remains is generated at run time into a temporary file and
//! elaborated by `lake env lean`, inheriting the repository's pinned toolchain the
//! same way CI does. It walks `env.constants`, and for each `Grass` declaration
//! emits one tab-separated record naming the declaration, its `private`-unmangled
//! name, the attributes that make its compiled behaviour differ from its logical
//! definition, and the axioms `collectAxioms` reports. It decides nothing.
//!
//! Its own helpers live in `GrassToolsAxiomAudit` rather than under `Grass`, which
//! is the one behavioural difference from `Tools/AxiomAudit.lean` that shows up in
//! the passing line. That file declared `allowedAxioms`, `userFacing`, `isAudited`,
//! `compiledOverride` and `modulesOnDisk` in `Grass.Tools`, so `isAudited` matched
//! them and the audit counted itself: six of the 12113 declarations it reported
//! were its own, `modulesOnDisk._unsafe_rec` among them. The count is supposed to
//! be a fact about the library, and an auditor inside its own audit is a way for a
//! change to the auditor to change the verdict. Taking the helpers out of the
//! namespace makes the port report 12107 on the same tree -- verified by dumping
//! both audited name sets and diffing them: they agree exactly, on every name, once
//! each tool's own six or three helpers are set aside.
//!
//! # Coverage is checked, not assumed
//!
//! An explicit import list is a coverage hazard, and in `Tools/AxiomAudit.lean` it
//! failed in exactly the predictable way: within a day of being written it had
//! fallen six modules behind the tree, and a maximally false axiom in an unimported
//! module passed both that tool and `lake build` with exit 0. A gate that silently
//! stops covering the newest code is worse than no gate, because the green run
//! still reads as assurance.
//!
//! The Lean file could not fix that itself -- Lean has no dynamic import, so the
//! list had to be written out by hand and guarded by a check that compared it
//! against `Grass/` on disk. Generating the Lean removes the constraint that
//! created the hazard: [`modules_on_disk`] walks the tree and [`lean_source`]
//! writes an `import` for every module it finds, so the list cannot be stale.
//!
//! The comparison is kept anyway. The generated snippet reports
//! `env.header.moduleNames` back, and [`verdict`] still fails if any module found
//! on disk is absent from it. It should now be unfalsifiable; a check that has
//! become unfalsifiable by construction is worth a few lines, because the
//! construction is what would break first.
//!
//! Importing every leaf is what `docs/OLEAN_SHARDING.md` §2 forbids for an
//! aggregate certificate. That rule is about proof aggregates whose types grow with
//! their descendants. This is a diagnostic that must see everything by
//! construction, produces no theorem, and is not on the path to `VerifiedProgram`.
//!
//! # An audit of nothing is not a clean audit
//!
//! `Tools/AxiomAudit.lean` reported success whenever its findings list was empty,
//! including when it had examined no declarations at all. With a hand-written
//! import list that took a deliberate edit to arrange; with a generated one an
//! empty or missing `Grass/` produces an empty import list, an empty environment
//! and the sentence "0 Grass declarations across 0 modules, no axiom outside the
//! allowlist", which reads as assurance and carries none. [`verdict`] refuses it.
//! See `audit_of_zero_declarations_is_refused`.
//!
//! Exit status is 1 on any finding, on a coverage gap, on an empty audit, and on
//! any failure to obtain the record set.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// The reviewed logical-foundation allowlist.
///
/// Exactly the three constants `docs/FOUNDATION.md` §3 permits, by their toolchain
/// declaration names. Adding to this list is a trust-boundary change and requires
/// the review that section demands, not an edit here.
const ALLOWED_AXIOMS: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

/// How the allowlist is rendered inside the failure message.
///
/// `Tools/AxiomAudit.lean` interpolated a `List Name` into its error, and
/// `MessageData` renders that as a bracketed comma-separated list. The sentence a
/// reader sees is unchanged.
fn allowed_axioms_display() -> String {
    format!("[{}]", ALLOWED_AXIOMS.join(", "))
}

// ---------------------------------------------------------------------------
// The record set the generated Lean produces.
// ---------------------------------------------------------------------------

/// One audited declaration, as the generated Lean reported it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Decl {
    /// The name the declaration is stored under, `private` mangling and all.
    stored: String,
    /// The name it is written under.
    ///
    /// A `private` declaration is stored as `_private.<module>.<n>.<real name>`,
    /// whose first component is `_private` rather than `Grass`. Testing the
    /// namespace on the stored name therefore skipped every private declaration in
    /// the library -- 111 in the x86 tree alone, including proof-carrying theorems.
    /// Stripping the mangling first is what puts them back inside the audit, and
    /// the generated Lean does it with `privateToUserName?` before deciding whether
    /// a declaration is in scope.
    user: String,
    /// `true` when the declaration is `unsafe`; §3 names "unsafe declarations used
    /// as proof".
    is_unsafe: bool,
    /// The attribute making this declaration's compiled behaviour differ from its
    /// logical definition, if any. See [`Report::override_findings`].
    compiled_override: Option<String>,
    /// Every axiom `collectAxioms` reported for this declaration.
    axioms: Vec<String>,
}

/// Everything the generated Lean reported, before any judgement is applied.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Report {
    /// `env.header.moduleNames`: what the elaborated file actually imported.
    imported: BTreeSet<String>,
    /// One entry per `Grass` declaration, in the order the environment yielded them.
    decls: Vec<Decl>,
}

impl Report {
    /// Declarations carrying an attribute that severs the compiled definition from
    /// the proved one.
    ///
    /// `docs/FOUNDATION.md` §3 is about what a proof may depend on, and this is the
    /// same question one step out. Every differential in this repository generates
    /// its corpus by *executing* a Grass definition through `lake env lean --run`,
    /// while every theorem is about the definition the kernel sees.
    /// `@[implemented_by]`, `@[extern]` and `@[csimp]` are exactly the three ways to
    /// make those two objects different.
    ///
    /// A reviewer demonstrated the consequence: an `opcodeTable` whose `0x83` row was
    /// poisoned to the wrong immediate size, with `@[implemented_by]` pointing at an
    /// untouched copy, passed the build, both audits, the ledger and all four
    /// differentials -- including the decoder differential written specifically to
    /// catch that mutation. It produces no axiom, no warning and no `unsafe` marker,
    /// so nothing else here would ever notice.
    ///
    /// None of the three is forbidden in general; they are forbidden on declarations
    /// this repository's assurance rests on, which is every `Grass` declaration.
    ///
    /// Reported under the written name rather than the stored one, as
    /// `Tools/AxiomAudit.lean` did.
    fn override_findings(&self) -> Vec<(&str, &str)> {
        let mut found: Vec<(&str, &str)> = self
            .decls
            .iter()
            .filter_map(|d| {
                d.compiled_override
                    .as_deref()
                    .map(|attr| (d.user.as_str(), attr))
            })
            .collect();
        found.sort_unstable();
        found
    }

    /// Declarations marked `unsafe`, under the stored name, as
    /// `Tools/AxiomAudit.lean` reported them.
    fn unsafe_findings(&self) -> Vec<&str> {
        let mut found: Vec<&str> = self
            .decls
            .iter()
            .filter(|d| d.is_unsafe)
            .map(|d| d.stored.as_str())
            .collect();
        found.sort_unstable();
        found
    }

    /// Every (declaration, axiom) pair outside the allowlist, under the stored
    /// name, as `Tools/AxiomAudit.lean` reported them.
    fn axiom_findings(&self) -> Vec<(&str, &str)> {
        let mut found: Vec<(&str, &str)> = self
            .decls
            .iter()
            .flat_map(|d| {
                d.axioms
                    .iter()
                    .filter(|used| !ALLOWED_AXIOMS.contains(&used.as_str()))
                    .map(move |used| (d.stored.as_str(), used.as_str()))
            })
            .collect();
        found.sort_unstable();
        found
    }
}

/// Parse the tab-separated record set the generated Lean writes.
///
/// The grammar is three record kinds, one per line:
///
/// - `M<TAB>module` -- one imported module.
/// - `D<TAB>stored<TAB>written<TAB>flags<TAB>axioms` -- one audited declaration,
///   where `flags` and `axioms` are comma-separated or `-` for empty.
/// - `Z<TAB>count` -- the terminator, carrying the number of `D` records.
///
/// The terminator is the point of the format. A Lean process killed part-way
/// through writing, or a disk that filled, would otherwise hand back a short record
/// set that parses cleanly and audits a prefix of the library -- the same silent
/// under-coverage the import list once had. A missing or disagreeing `Z` is a hard
/// error.
fn parse_records(text: &str) -> Result<Report, String> {
    let mut report = Report::default();
    let mut terminator: Option<usize> = None;
    for (index, line) in text.lines().enumerate() {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() {
            continue;
        }
        let number = index + 1;
        if terminator.is_some() {
            return Err(format!(
                "axiom audit: record {number} follows the terminator: {line:?}"
            ));
        }
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["M", module] => {
                report.imported.insert((*module).to_string());
            }
            ["D", stored, user, flags, axioms] => {
                let flags = split_list(flags);
                report.decls.push(Decl {
                    stored: (*stored).to_string(),
                    user: (*user).to_string(),
                    is_unsafe: flags.iter().any(|f| f == "unsafe"),
                    compiled_override: flags.iter().find(|f| f.starts_with("@[")).map(String::from),
                    axioms: split_list(axioms),
                });
            }
            ["Z", count] => {
                terminator = Some(count.parse::<usize>().map_err(|err| {
                    format!("axiom audit: record {number} has an unreadable count: {err}")
                })?);
            }
            _ => {
                return Err(format!(
                    "axiom audit: record {number} is not a record this tool wrote: {line:?}"
                ))
            }
        }
    }
    match terminator {
        None => Err(
            "axiom audit: the declaration record set has no terminator, so it is a prefix of the \
             library rather than the library. Refusing to audit part of the tree and report on all \
             of it."
                .to_string(),
        ),
        Some(count) if count != report.decls.len() => Err(format!(
            "axiom audit: the record set claims {count} declarations and carries {}, so it was \
             truncated in transit.",
            report.decls.len()
        )),
        Some(_) => Ok(report),
    }
}

/// A comma-separated field, with `-` standing for the empty list.
fn split_list(field: &str) -> Vec<String> {
    if field == "-" {
        Vec::new()
    } else {
        field.split(',').map(str::to_string).collect()
    }
}

// ---------------------------------------------------------------------------
// The verdict.
// ---------------------------------------------------------------------------

/// The whole judgement, over a record set and the module list from disk.
///
/// `Ok` carries the line a passing run prints; `Err` carries the text a failing
/// run prints, and every one of them is the sentence `Tools/AxiomAudit.lean`
/// printed for the same condition.
///
/// The order of the checks is that file's order -- coverage, then compiled
/// overrides, then `unsafe`, then axioms -- with the empty-audit refusal inserted
/// directly after coverage, where "did this examine anything" belongs.
fn verdict(report: &Report, on_disk: &[String]) -> Result<String, String> {
    let missing: Vec<&String> = on_disk
        .iter()
        .filter(|m| !report.imported.contains(*m))
        .collect();
    if !missing.is_empty() {
        let mut message = String::from(
            "axiom audit coverage gap: these modules exist under Grass/ but were not imported by \
             the generated audit, so their declarations were never scanned:\n",
        );
        for module in missing {
            let _ = writeln!(message, "  {module}");
        }
        return Err(message.trim_end().to_string());
    }

    // The vacuous-pass refusal. See the module comment.
    if on_disk.is_empty() || report.decls.is_empty() {
        return Err(format!(
            "axiom audit: examined {} declarations across {} modules under Grass/, so it audited \
             nothing.\nRefusing to report a clean axiom audit of an empty scan: run this from the \
             repository root.",
            report.decls.len(),
            on_disk.len()
        ));
    }

    let overrides = report.override_findings();
    if !overrides.is_empty() {
        let mut message = String::from(
            "axiom audit failed: a Grass declaration's compiled behaviour is allowed to differ \
             from its logical definition. Every differential in this repository measures the \
             compiled definition while every theorem is about the logical one, so this severs the \
             two.\n",
        );
        for (name, attr) in overrides {
            let _ = writeln!(message, "  {name} carries {attr}");
        }
        return Err(message.trim_end().to_string());
    }

    let unsafes = report.unsafe_findings();
    if !unsafes.is_empty() {
        let mut message = String::from(
            "axiom audit failed; docs/FOUNDATION.md section 3 forbids unsafe declarations used as \
             proof:\n",
        );
        for name in unsafes {
            let _ = writeln!(message, "  {name}");
        }
        return Err(message.trim_end().to_string());
    }

    let axioms = report.axiom_findings();
    if !axioms.is_empty() {
        let mut message = format!(
            "axiom audit failed; docs/FOUNDATION.md section 3 permits only {}\n",
            allowed_axioms_display()
        );
        for (name, used) in axioms {
            let _ = writeln!(message, "  {name} depends on {used}");
        }
        return Err(message.trim_end().to_string());
    }

    Ok(format!(
        "axiom audit: {} Grass declarations across {} modules, no axiom outside the allowlist, no \
         unsafe declaration, no compiled override",
        report.decls.len(),
        on_disk.len()
    ))
}

// ---------------------------------------------------------------------------
// The tree walk, and the Lean it generates.
// ---------------------------------------------------------------------------

/// Every Lean module found under `root` on disk, as a dotted module name.
///
/// `Tools/AxiomAudit.lean` used this to *check* its hand-written import list; here
/// it *is* the import list, and the check is what remains of the older
/// arrangement. Sorted so the generated source, and therefore any Lean diagnostic
/// quoting a line of it, is reproducible.
fn modules_on_disk(root: &Path, prefix: &str) -> Result<Vec<String>, String> {
    let mut found = Vec::new();
    let mut stack = vec![(root.to_path_buf(), prefix.to_string())];
    while let Some((dir, dotted)) = stack.pop() {
        let entries = fs::read_dir(&dir).map_err(|err| format!("{}: {err}", dir.display()))?;
        for entry in entries {
            let entry = entry.map_err(|err| format!("{}: {err}", dir.display()))?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let file_type = entry
                .file_type()
                .map_err(|err| format!("{}: {err}", entry.path().display()))?;
            if file_type.is_dir() {
                stack.push((entry.path(), format!("{dotted}.{name}")));
            } else if let Some(stem) = name.strip_suffix(".lean") {
                found.push(format!("{dotted}.{stem}"));
            }
        }
    }
    found.sort();
    Ok(found)
}

/// Whether a module name can be written after `import` without quoting.
///
/// Generating an import list means a file name reaches the elaborator as syntax.
/// Every module in this tree is `UpperCamelCase`, but a file named `x-y.lean`
/// would produce a parse error inside a generated file the reader never sees, and
/// the diagnosis would be a puzzle. Refusing it by name is the self-healing
/// version of that failure.
fn is_plain_module_name(name: &str) -> bool {
    !name.is_empty()
        && name.split('.').all(|part| {
            let mut chars = part.chars();
            matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
        })
}

/// A Lean string literal for `path`, so a Windows path survives being pasted into
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

/// The Lean meta-program, with `modules` imported and the record set written to
/// `out`.
///
/// This is the whole of what has to be Lean. `privateToUserName?`,
/// `ConstantInfo.isUnsafe`, `Compiler.getImplementedBy?`, `isExtern` and
/// `collectAxioms` are all queries against the environment the kernel built, and
/// none of them has an answer outside it. The predicates are carried over from
/// `Tools/AxiomAudit.lean` unchanged, including the `run_cmd` self-test that
/// catches an `isAudited` that has stopped seeing authored underscore-prefixed
/// names.
fn lean_source(modules: &[String], out: &Path) -> String {
    let imports = modules
        .iter()
        .map(|m| format!("import {m}\n"))
        .collect::<String>();
    let out_literal = lean_string_literal(&out.to_string_lossy());
    format!(
        r#"import Lean
{imports}
open Lean

namespace GrassToolsAxiomAudit

/-- The name a declaration is written under, with any `private` mangling removed. -/
def userFacing (name : Name) : Name := (privateToUserName? name).getD name

/-- Whether a declaration belongs to the audited namespace. -/
def isAudited (name : Name) : Bool := (`Grass).isPrefixOf (userFacing name)

run_cmd do
  unless isAudited `Grass._authoredUnderscoreProbe do
    throwError "axiom audit would skip an authored underscore-prefixed Grass declaration"

/--
Attributes that make a declaration's compiled behaviour differ from its logical
definition. Reported, not judged; the caller decides what they mean.
-/
def compiledOverride (env : Environment) (name : Name) : Option String :=
  if (Lean.Compiler.getImplementedBy? env name).isSome then
    some "@[implemented_by]"
  else if Lean.isExtern env name then
    some "@[extern]"
  else
    Option.none

end GrassToolsAxiomAudit

open GrassToolsAxiomAudit in
run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  let mut lines : Array String := #[]
  for m in env.header.moduleNames do
    lines := lines.push ("M\t" ++ toString m)
  let mut audited : Nat := 0
  for (name, info) in env.constants.toList do
    unless isAudited name do continue
    audited := audited + 1
    let unsafeFlag := if info.isUnsafe then ["unsafe"] else []
    let overrideFlag :=
      match compiledOverride env name with
      | some attr => [attr]
      | Option.none => []
    let flags := unsafeFlag ++ overrideFlag
    let flagField := if flags.isEmpty then "-" else String.intercalate "," flags
    let axioms ← Elab.Command.liftCoreM (collectAxioms name)
    let axiomField :=
      if axioms.isEmpty then "-"
      else String.intercalate "," (axioms.toList.map toString)
    lines := lines.push
      ("D\t" ++ toString name ++ "\t" ++ toString (userFacing name) ++ "\t" ++ flagField
        ++ "\t" ++ axiomField)
  lines := lines.push ("Z\t" ++ toString audited)
  IO.FS.writeFile {out_literal} (String.intercalate "\n" lines.toList ++ "\n")
"#
    )
}

// ---------------------------------------------------------------------------
// Running it.
// ---------------------------------------------------------------------------

/// Elaborate `source` under the repository's toolchain and read back the records.
///
/// `lake env lean` is how `.github/workflows/library.yml` invoked
/// `Tools/AxiomAudit.lean`, and it is what puts the built `.olean` files on
/// `LEAN_PATH`; the working directory therefore has to be the repository root,
/// exactly as it did before.
///
/// The record set goes to a file rather than to standard output so that a Lean
/// diagnostic can never be mistaken for a record, and a record can never be
/// mistaken for a diagnostic. A non-zero exit, or a missing file, surfaces Lean's
/// own output verbatim -- that is the message a reader can act on.
fn elaborate(build_source: impl FnOnce(&Path) -> String) -> Result<String, String> {
    let dir = tempfile::Builder::new()
        .prefix("grass-axiom-audit")
        .tempdir()
        .map_err(|err| format!("axiom audit: could not create a working directory: {err}"))?;
    let script: PathBuf = dir.path().join("AxiomAuditProbe.lean");
    let records: PathBuf = dir.path().join("records.tsv");
    fs::write(&script, build_source(&records))
        .map_err(|err| format!("axiom audit: could not write {}: {err}", script.display()))?;

    let output = Command::new("lake")
        .args(["env", "lean"])
        .arg(&script)
        .output()
        .map_err(|err| {
            format!(
                "axiom audit: could not run `lake env lean`: {err}\nThis audit needs the pinned \
                 toolchain and must be run from the repository root."
            )
        })?;
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    if !output.status.success() {
        return Err(format!(
            "axiom audit: the Lean side of the audit failed, so nothing was audited:\n{stdout}{stderr}"
        ));
    }
    fs::read_to_string(&records).map_err(|err| {
        format!(
            "axiom audit: the Lean side produced no record set ({err}), so nothing was \
             audited:\n{stdout}{stderr}"
        )
    })
}

fn main() -> ExitCode {
    match run() {
        Ok(message) => {
            println!("{message}");
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<String, String> {
    let root = Path::new("Grass");
    if !root.is_dir() {
        let cwd = std::env::current_dir()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|err| format!("<unavailable: {err}>"));
        return Err(format!(
            "axiom audit: there is no Grass/ directory under {cwd}, so there is nothing to \
             audit.\nRefusing to report a clean axiom audit of an empty scan: run this from the \
             repository root."
        ));
    }
    let modules = modules_on_disk(root, "Grass")?;
    if let Some(bad) = modules.iter().find(|m| !is_plain_module_name(m)) {
        return Err(format!(
            "axiom audit: {bad} is not a module name that can be imported without quoting, so the \
             generated audit could not be built. Rename the file, or teach `lean_source` to quote."
        ));
    }
    // `elaborate` owns the temporary directory, so it is what knows where the
    // record set will land.
    let records = elaborate(|out| lean_source(&modules, out))?;
    verdict(&parse_records(&records)?, &modules)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decl(stored: &str, axioms: &[&str]) -> Decl {
        Decl {
            stored: stored.to_string(),
            user: stored.to_string(),
            is_unsafe: false,
            compiled_override: None,
            axioms: axioms.iter().map(|a| (*a).to_string()).collect(),
        }
    }

    fn report(decls: Vec<Decl>, modules: &[&str]) -> Report {
        Report {
            imported: modules.iter().map(|m| (*m).to_string()).collect(),
            decls,
        }
    }

    // --- the verdict ------------------------------------------------------

    #[test]
    fn allowlisted_axioms_pass_and_the_line_counts_what_was_seen() {
        let r = report(
            vec![
                decl("Grass.a", &["propext"]),
                decl("Grass.b", &["Classical.choice", "Quot.sound"]),
            ],
            &["Grass.A", "Grass.B"],
        );
        let line = verdict(&r, &["Grass.A".into(), "Grass.B".into()]).expect("clean");
        assert_eq!(
            line,
            "axiom audit: 2 Grass declarations across 2 modules, no axiom outside the allowlist, \
             no unsafe declaration, no compiled override"
        );
    }

    #[test]
    fn an_axiom_outside_the_allowlist_fails() {
        let r = report(vec![decl("Grass.a", &["sorryAx"])], &["Grass.A"]);
        let message = verdict(&r, &["Grass.A".into()]).expect_err("sorryAx must fail the gate");
        assert!(message.starts_with("axiom audit failed; docs/FOUNDATION.md section 3 permits only [propext, Classical.choice, Quot.sound]"), "{message}");
        assert!(
            message.contains("  Grass.a depends on sorryAx"),
            "{message}"
        );
    }

    #[test]
    fn an_unsafe_declaration_fails_before_the_axiom_report() {
        // Both findings are present; §3's own ordering puts `unsafe` first.
        let mut bad = decl("Grass.a", &["sorryAx"]);
        bad.is_unsafe = true;
        let r = report(vec![bad], &["Grass.A"]);
        let message = verdict(&r, &["Grass.A".into()]).expect_err("unsafe must fail the gate");
        assert!(
            message.contains("forbids unsafe declarations used as proof"),
            "{message}"
        );
        assert!(message.contains("  Grass.a"), "{message}");
    }

    #[test]
    fn a_compiled_override_fails_first_of_all() {
        let mut bad = decl("Grass.opcodeTable", &["sorryAx"]);
        bad.is_unsafe = true;
        bad.compiled_override = Some("@[implemented_by]".to_string());
        let r = report(vec![bad], &["Grass.A"]);
        let message = verdict(&r, &["Grass.A".into()]).expect_err("an override must fail the gate");
        assert!(
            message.starts_with("axiom audit failed: a Grass declaration's compiled behaviour"),
            "{message}"
        );
        assert!(
            message.contains("  Grass.opcodeTable carries @[implemented_by]"),
            "{message}"
        );
    }

    #[test]
    fn an_override_is_reported_under_the_written_name() {
        // `Tools/AxiomAudit.lean` reported overrides through `userFacing` and the
        // other two findings through the stored name. Preserved, oddity included.
        let bad = Decl {
            stored: "_private.Grass.ISA.X86.Decode.0.Grass.ISA.X86.helper".to_string(),
            user: "Grass.ISA.X86.helper".to_string(),
            is_unsafe: false,
            compiled_override: Some("@[extern]".to_string()),
            axioms: Vec::new(),
        };
        let r = report(vec![bad], &["Grass.A"]);
        let message = verdict(&r, &["Grass.A".into()]).expect_err("an override must fail the gate");
        assert!(
            message.contains("  Grass.ISA.X86.helper carries @[extern]"),
            "{message}"
        );
        assert!(!message.contains("_private"), "{message}");
    }

    #[test]
    fn a_module_on_disk_that_was_not_imported_is_a_coverage_gap() {
        let r = report(vec![decl("Grass.a", &[])], &["Grass.A"]);
        let message = verdict(&r, &["Grass.A".into(), "Grass.B".into()])
            .expect_err("an unscanned module must fail the gate");
        assert!(
            message.starts_with("axiom audit coverage gap:"),
            "{message}"
        );
        assert!(message.contains("  Grass.B"), "{message}");
        assert!(!message.contains("  Grass.A"), "{message}");
    }

    // --- the vacuous-pass refusal ----------------------------------------

    #[test]
    fn audit_of_zero_declarations_is_refused() {
        // The failure this port exists to close. Every finding list is empty, so
        // `Tools/AxiomAudit.lean` would have printed "0 Grass declarations across 0
        // modules, no axiom outside the allowlist" and exited 0.
        let message = verdict(&Report::default(), &[])
            .expect_err("an audit that examined nothing must not report success");
        assert!(message.contains("audited nothing"), "{message}");
        assert!(
            message.contains("Refusing to report a clean axiom audit"),
            "{message}"
        );
        assert!(
            !message.contains("no axiom outside the allowlist"),
            "an empty scan must never borrow the success line: {message}"
        );
    }

    #[test]
    fn modules_present_but_no_declarations_is_also_refused() {
        // `isAudited` ceasing to match -- a namespace rename, a broken
        // `privateToUserName?` -- empties the audit without emptying the tree.
        let r = report(Vec::new(), &["Grass.A"]);
        let message = verdict(&r, &["Grass.A".into()])
            .expect_err("zero audited declarations must not report success");
        assert!(message.contains("examined 0 declarations"), "{message}");
    }

    #[test]
    fn an_empty_grass_directory_yields_no_modules() {
        // The other half of the falsification: the walk really does return nothing,
        // so `verdict` really does meet the empty case above.
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path().join("Grass");
        fs::create_dir_all(root.join("Memory")).expect("mkdir");
        fs::write(root.join("notes.md"), "").expect("write");
        assert!(modules_on_disk(&root, "Grass").expect("walk").is_empty());
    }

    // --- the record format ------------------------------------------------

    #[test]
    fn records_parse_into_the_report_they_describe() {
        let text = "M\tGrass.A\nD\tGrass.a\tGrass.a\t-\tpropext\n\
                    D\t_private.Grass.A.0.Grass.b\tGrass.b\tunsafe,@[extern]\t-\nZ\t2\n";
        let parsed = parse_records(text).expect("well-formed");
        assert_eq!(parsed.imported, BTreeSet::from(["Grass.A".to_string()]));
        assert_eq!(parsed.decls.len(), 2);
        assert_eq!(parsed.decls[0].axioms, vec!["propext".to_string()]);
        assert!(parsed.decls[1].is_unsafe);
        assert_eq!(
            parsed.decls[1].compiled_override.as_deref(),
            Some("@[extern]")
        );
        assert_eq!(parsed.decls[1].user, "Grass.b");
        assert!(parsed.decls[1].axioms.is_empty());
    }

    #[test]
    fn a_truncated_record_set_is_refused_rather_than_audited() {
        // Without the terminator this parses cleanly as an audit of one
        // declaration, which is the silent under-coverage the import list once had.
        let short = "M\tGrass.A\nD\tGrass.a\tGrass.a\t-\t-\n";
        let message = parse_records(short).expect_err("a set with no terminator must be refused");
        assert!(message.contains("no terminator"), "{message}");

        let disagreeing = "D\tGrass.a\tGrass.a\t-\t-\nZ\t9\n";
        let message = parse_records(disagreeing).expect_err("a disagreeing count must be refused");
        assert!(message.contains("truncated in transit"), "{message}");
    }

    #[test]
    fn an_unrecognised_record_is_refused() {
        assert!(parse_records("hello\nZ\t0\n").is_err());
        assert!(parse_records("Z\t0\nD\tGrass.a\tGrass.a\t-\t-\n").is_err());
    }

    // --- generation -------------------------------------------------------

    #[test]
    fn the_generated_source_imports_every_module_found_on_disk() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path().join("Grass");
        fs::create_dir_all(root.join("ISA/X86")).expect("mkdir");
        fs::write(root.join("Certificate.lean"), "").expect("write");
        fs::write(root.join("ISA/X86/Decode.lean"), "").expect("write");
        fs::write(root.join("ISA/X86/notes.txt"), "").expect("write");
        let modules = modules_on_disk(&root, "Grass").expect("walk");
        assert_eq!(
            modules,
            vec![
                "Grass.Certificate".to_string(),
                "Grass.ISA.X86.Decode".to_string()
            ]
        );

        let source = lean_source(&modules, Path::new("out.tsv"));
        assert!(source.contains("import Grass.Certificate\n"));
        assert!(source.contains("import Grass.ISA.X86.Decode\n"));
        // The list can no longer be stale, which is the point of generating it.
        assert_eq!(source.matches("\nimport Grass.").count(), 2);
    }

    #[test]
    fn a_module_name_needing_quotes_is_refused_by_name() {
        assert!(is_plain_module_name("Grass.ISA.X86.Decode"));
        assert!(is_plain_module_name("Grass.Std.Logical.Vec"));
        assert!(!is_plain_module_name("Grass.x-y"));
        assert!(!is_plain_module_name("Grass.9Lives"));
        assert!(!is_plain_module_name("Grass."));
    }

    #[test]
    fn a_windows_path_survives_becoming_a_lean_literal() {
        assert_eq!(
            lean_string_literal(r"C:\tmp\records.tsv"),
            "\"C:\\\\tmp\\\\records.tsv\""
        );
        assert_eq!(lean_string_literal("say \"hi\""), "\"say \\\"hi\\\"\"");
    }

    #[test]
    fn the_allowlist_is_rendered_the_way_the_message_reads() {
        assert_eq!(
            allowed_axioms_display(),
            "[propext, Classical.choice, Quot.sound]"
        );
    }
}
