//! Check that every `Vec`-returning operation states what it does to `length`
//! and to `get?`.
//!
//! `docs/STDLIB_IMPLEMENTATION_PLAN.md` decision 6 requires that every operation
//! returning a `Vec` state a law computing the result's `length` **and** a law
//! computing the result's `get?`, in terms of its arguments'. This tool checks it.
//!
//! # Why it is a program and not a paragraph
//!
//! The rule has been rewritten three times. Every version was stated in prose, and
//! every version was violated in the same commit that stated it -- the "at least
//! one law" rule shipped alongside `truncate` and `clear`, which had none; the
//! "determination" rule shipped alongside an internal inconsistency about
//! `splitAt`; and the coverage rule itself shipped alongside `Vec.sum` and
//! `Vec.count`, which had no laws at all, with `sum` on the right-hand side of
//! `Vec.length_flatten` where every consumer of that law would meet it.
//!
//! That is not carelessness three times. It is what an unenforced rule does to a
//! library changing at this rate, and it was adversarial review rather than the
//! author that caught each one. `axiom_audit` and `docstring_audit` exist for the
//! same reason and their module comments say so.
//!
//! # What it checks, and what it deliberately does not
//!
//! A declaration is an **operation** if it is a `def` in `Grass.Std.Logical.Vec`
//! whose result type is a `Vec`. For each, the audit looks for a theorem somewhere
//! in the environment whose statement applies `Vec.length` to a term headed by
//! that operation, and likewise for `Vec.get?`.
//!
//! It has been attacked, and it failed once. The first version accepted an
//! operation carrying `(f v i).length = (f v i).length` and
//! `(f v i).get? j = (f v i).get? j` -- two `rfl` self-laws -- and counted it as
//! covered. That is the same attack adversarial review had used to break the
//! *prose* rule, and it worked on the checker too. `observesNonVacuously` is the
//! fix: an equation counts only if the side that does not observe `op` also does
//! not mention it. Three negative tests now pass -- no laws, a length law without
//! a `get?` law, and two vacuous laws -- each of which compiles cleanly under
//! `lake build`.
//!
//! Four deliberate limits, stated because a checker that overstates its reach is
//! worse than none:
//!
//! - A law stated over the `v[i]?` notation rather than `Vec.get?` would not be
//!   seen, since `GetElem?.getElem?` is a different constant. No law in the library
//!   is currently written that way, but the audit would produce a false failure if
//!   one were.
//! - It does not check that a law is *correct*, only that it exists and is about
//!   the right thing. The kernel checks correctness.
//! - It does not reach operations returning `Bool`, `Nat`, `Option`, or `Prop` --
//!   roughly half the module. Decision 6's clause (i) is phrased over `length` and
//!   `get?` of a result, which presupposes the result is a `Vec`. Those operations
//!   are counted and listed as outside the bar rather than silently passed, so the
//!   number is visible.
//! - It does not implement clause (ii), the `empty`/`push` recursion, nor the alias
//!   clause. Operations that pass on those are named in [`RECURSION_OR_ALIAS`] and
//!   the exemption is explicit, which is the point: an exemption in a list is
//!   reviewable, an exemption in prose is not.
//!
//! # Why a Rust program that writes Lean
//!
//! Deciding whether a theorem's *statement* observes an operation is a question
//! about an elaborated `Expr`, so `observes`, `mentions` and `observesNonVacuously`
//! have to run inside Lean; they are carried over from `Tools/CoverageAudit.lean`
//! unchanged. Everything else is judgement about a table of answers, and it moved
//! here: the exemption list, which operations count, what the verdict is, how the
//! report reads, and whether the run examined enough to mean anything.
//!
//! The Lean is generated at run time into a temporary file and elaborated by
//! `lake env lean`, inheriting the repository's pinned toolchain the same way CI
//! does. It imports exactly `Grass.Std.Logical.Vec` and `Grass.Std.Logical.Order`,
//! as the Lean file did: the theorem search sees the environment those two pull
//! in, and widening it would silently *weaken* the audit by admitting laws from
//! further away.
//!
//! # An audit of nothing is not a clean audit
//!
//! `Tools/CoverageAudit.lean` reported success whenever its `missing` list was
//! empty, and `missing` is empty when there are no operations to check. A renamed
//! namespace, a `Vec` that stops being called `Vec`, an import that stops
//! resolving: each produces "0 Vec-returning operations each carry a length law
//! and a get? law" and exit 0, which reads as assurance and carries none.
//! [`verdict`] refuses it. See `audit_of_zero_operations_is_refused`.
//!
//! Exit status is 1 on any finding, on an empty audit, and on any failure to
//! obtain the record set.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

/// The namespace the bar is phrased over.
const VEC_NAMESPACE: &str = "Grass.Std.Logical.Vec";

/// Operations that satisfy decision 6 by its clause (ii) or its alias clause
/// rather than by a `length`/`get?` pair, with the reason.
///
/// Listed rather than inferred, so that adding one is a reviewable edit.
/// Adversarial review found that the alias clause as originally worded admitted a
/// cycle -- two operations each citing the other and neither carrying a law -- so
/// an alias exemption is only as good as the fact that a human wrote it down here.
///
/// The `append` entry is the first thing this audit found, and it is worth
/// recording what kind of finding it is. `Vec.length_append` and the two
/// `get?_append_*` laws exist, but every one is stated over `v ++ w`, which
/// elaborates through the `Append` instance rather than as an application of
/// `Vec.append`. So the laws cover the operation *as consumers write it* and leave
/// the bare name uncovered.
///
/// That is a naming observation rather than a missing law, which is why it is an
/// exemption with a reason instead of a weakening of the check. The alternative --
/// teaching the audit to see through instance applications -- would make it accept
/// a class of genuine gaps in exchange for tidying one false one.
const RECURSION_OR_ALIAS: &[(&str, &str)] = &[
    (
        "Grass.Std.Logical.Vec.foldl",
        "clause (ii): foldl_empty, foldl_push",
    ),
    (
        "Grass.Std.Logical.Vec.foldr",
        "clause (ii): foldr_empty, foldr_push",
    ),
    (
        "Grass.Std.Logical.Vec.flatten",
        "clause (ii): flatten_empty, flatten_push",
    ),
    (
        "Grass.Std.Logical.Vec.pop?",
        "clause (ii): pop?_empty, pop?_push",
    ),
    (
        "Grass.Std.Logical.Vec.truncate",
        "alias: truncate_eq_take, and take passes (i)",
    ),
    (
        "Grass.Std.Logical.Vec.clear",
        "alias: clear_eq_empty, and empty passes (i)",
    ),
    (
        "Grass.Std.Logical.Vec.splitAt",
        "alias: splitAt_eq, and take/drop pass (i)",
    ),
    (
        "Grass.Std.Logical.Vec.fromList",
        "the constructor; toList_fromList characterises it",
    ),
    (
        "Grass.Std.Logical.Vec.append",
        "laws stated over the `++` notation: length_append, get?_append_left, get?_append_right",
    ),
];

// ---------------------------------------------------------------------------
// The record set the generated Lean produces.
// ---------------------------------------------------------------------------

/// One operation the bar reaches, with what the theorem search found for it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Operation {
    name: String,
    /// A theorem states `Vec.length` of a term headed by this operation, against a
    /// side that does not mention the operation.
    has_length_law: bool,
    /// The same for `Vec.get?`.
    has_get_law: bool,
}

/// Everything the generated Lean reported, before any judgement is applied.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Report {
    /// The operations actually checked -- `Vec`-returning `def`s that the exemption
    /// list did not name.
    checked: Vec<Operation>,
    /// `Vec`-returning `def`s the exemption list did name, so that a name in
    /// [`RECURSION_OR_ALIAS`] which no longer matches anything can be noticed.
    exempted: BTreeSet<String>,
    /// `def`s in the namespace whose result is not a `Vec`; counted and reported so
    /// the size of the bar's blind spot is visible rather than implied.
    outside_bar: Vec<String>,
    /// How many theorem statements the search ran over.
    theorems: usize,
}

/// Parse the tab-separated record set the generated Lean writes.
///
/// The grammar is five record kinds, one per line:
///
/// - `O<TAB>name<TAB>0|1<TAB>0|1` -- a checked operation and its two answers.
/// - `A<TAB>name` -- an operation the exemption list matched.
/// - `X<TAB>name` -- a namespace `def` whose result is not a `Vec`.
/// - `T<TAB>count` -- how many theorem statements were scanned.
/// - `Z<TAB>checked<TAB>exempt<TAB>outside` -- the terminator.
///
/// The terminator is the point of the format. A Lean process killed part-way
/// through, or a disk that filled, would otherwise hand back a short record set
/// that parses cleanly and reports a clean audit of the operations that happened to
/// be written first.
fn parse_records(text: &str) -> Result<Report, String> {
    let mut report = Report::default();
    let mut terminator: Option<(usize, usize, usize)> = None;
    for (index, line) in text.lines().enumerate() {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() {
            continue;
        }
        let number = index + 1;
        if terminator.is_some() {
            return Err(format!(
                "observation-coverage audit: record {number} follows the terminator: {line:?}"
            ));
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let flag = |field: &str| match field {
            "0" => Ok(false),
            "1" => Ok(true),
            other => Err(format!(
                "observation-coverage audit: record {number} has an unreadable flag {other:?}"
            )),
        };
        let count = |field: &str| {
            field.parse::<usize>().map_err(|err| {
                format!(
                    "observation-coverage audit: record {number} has an unreadable count: {err}"
                )
            })
        };
        match fields.as_slice() {
            ["O", name, length, get] => report.checked.push(Operation {
                name: (*name).to_string(),
                has_length_law: flag(length)?,
                has_get_law: flag(get)?,
            }),
            ["A", name] => {
                report.exempted.insert((*name).to_string());
            }
            ["X", name] => report.outside_bar.push((*name).to_string()),
            ["T", n] => report.theorems = count(n)?,
            ["Z", checked, exempt, outside] => {
                terminator = Some((count(checked)?, count(exempt)?, count(outside)?))
            }
            _ => {
                return Err(format!(
                    "observation-coverage audit: record {number} is not a record this tool wrote: \
                     {line:?}"
                ))
            }
        }
    }
    match terminator {
        None => Err(
            "observation-coverage audit: the record set has no terminator, so it covers some of \
             the operations rather than all of them. Refusing to audit part of the module and \
             report on all of it."
                .to_string(),
        ),
        Some((checked, exempt, outside))
            if (checked, exempt, outside)
                != (
                    report.checked.len(),
                    report.exempted.len(),
                    report.outside_bar.len(),
                ) =>
        {
            Err(format!(
                "observation-coverage audit: the record set claims ({checked}, {exempt}, \
                 {outside}) records and carries ({}, {}, {}), so it was truncated in transit.",
                report.checked.len(),
                report.exempted.len(),
                report.outside_bar.len()
            ))
        }
        Some(_) => Ok(report),
    }
}

// ---------------------------------------------------------------------------
// The verdict.
// ---------------------------------------------------------------------------

/// Why one operation fails the bar, in the words `Tools/CoverageAudit.lean` used.
fn shortfall(op: &Operation) -> Option<&'static str> {
    match (op.has_length_law, op.has_get_law) {
        (true, true) => None,
        (false, false) => Some("no length law and no get? law"),
        (false, true) => Some("no law computing its length"),
        (true, false) => Some("no law computing its get?"),
    }
}

/// Exemptions that name nothing the bar would have checked anyway.
///
/// Reported, not enforced. An inert exemption cannot weaken the audit -- nothing is
/// skipped that would otherwise be checked -- but it does leave a line in a list
/// whose whole value is that a human reviewed it, giving a reason that is not the
/// reason the operation is passing. `Tools/CoverageAudit.lean` could not notice
/// this at all, because it filtered by list membership and never asked whether a
/// member matched.
///
/// It fires on this tree, and the answer is worth recording. Five of the nine
/// entries in [`RECURSION_OR_ALIAS`] name declarations the bar never reached:
/// `foldl` and `foldr` return the accumulator, `pop?` returns an `Option`,
/// `splitAt` returns a pair -- so all four are classified outside the bar, not
/// exempted from it -- and `fromList` is the `Vec` structure's constructor, which
/// is a `ctorInfo` rather than a `defnInfo` and so was never a candidate. Only
/// `flatten`, `truncate`, `clear` and `append` are exemptions that do anything.
/// The clause (ii) reasons attached to the other five read as if they were
/// excusing a check that was never applied.
fn stale_exemptions(report: &Report) -> Vec<&'static str> {
    RECURSION_OR_ALIAS
        .iter()
        .map(|(name, _)| *name)
        .filter(|name| !report.exempted.contains(*name))
        .collect()
}

/// The whole judgement, over a record set.
///
/// `Ok` carries the line a passing run prints; `Err` carries the text a failing run
/// prints, and both are the sentences `Tools/CoverageAudit.lean` printed for the
/// same condition -- with the empty-audit refusal added, and a note about stale
/// exemptions appended where there are any.
fn verdict(report: &Report) -> Result<String, String> {
    // The vacuous-pass refusal. See the module comment.
    if report.checked.is_empty() {
        return Err(format!(
            "observation-coverage audit: found no Vec-returning operations to check in \
             {VEC_NAMESPACE} ({} exempt, {} outside the bar, {} theorems scanned), so it audited \
             nothing.\nRefusing to report clean observation coverage of an empty scan: run this \
             from the repository root.",
            report.exempted.len(),
            report.outside_bar.len(),
            report.theorems
        ));
    }
    if report.theorems == 0 {
        return Err(
            "observation-coverage audit: no theorem statements were scanned, so every operation \
             would be reported as uncovered for a reason that is not about the library. Refusing \
             to report on an empty theorem set."
                .to_string(),
        );
    }

    let mut missing: Vec<(&str, &str)> = report
        .checked
        .iter()
        .filter_map(|op| shortfall(op).map(|why| (op.name.as_str(), why)))
        .collect();
    missing.sort_unstable();

    if !missing.is_empty() {
        let mut message = String::from(
            "observation-coverage audit failed; docs/STDLIB_IMPLEMENTATION_PLAN.md decision 6 \
             requires a length law and a get? law for every Vec-returning operation:\n",
        );
        for (name, why) in missing {
            let _ = writeln!(message, "  {name}: {why}");
        }
        let _ = write!(message, "{}", stale_exemption_note(report));
        return Err(message.trim_end().to_string());
    }

    let mut message = format!(
        "observation-coverage audit: {} Vec-returning operations each carry a length law and a \
         get? law; {} exempt by clause (ii) or the alias clause; {} declarations outside the bar's \
         reach",
        report.checked.len(),
        RECURSION_OR_ALIAS.len(),
        report.outside_bar.len()
    );
    let _ = write!(message, "{}", stale_exemption_note(report));
    Ok(message.trim_end().to_string())
}

/// The note appended when an exemption matches nothing.
fn stale_exemption_note(report: &Report) -> String {
    let stale = stale_exemptions(report);
    if stale.is_empty() {
        return String::new();
    }
    let mut note = format!(
        "\nnote: {} of the {} exemptions name nothing this audit would otherwise have checked. \
         The bar reaches only Vec-returning `def`s, and these are not among them, so each exempts \
         nothing and its stated reason is not why the declaration is passing:\n",
        stale.len(),
        RECURSION_OR_ALIAS.len()
    );
    for name in stale {
        let _ = writeln!(note, "  {name}");
    }
    note
}

// ---------------------------------------------------------------------------
// The Lean it generates.
// ---------------------------------------------------------------------------

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

/// The Lean meta-program, with the exemption list baked in and the record set
/// written to `out`.
///
/// `observes`, `mentions`, `observesNonVacuously` and `returnsVec` are
/// `Tools/CoverageAudit.lean`'s, unchanged. They are here rather than in Rust
/// because each is a fold over an elaborated `Expr`, which exists only inside the
/// environment.
///
/// The exemption list is passed *in* so that Lean can skip the operations it names
/// rather than compute answers the caller will throw away. That matters: the
/// theorem search is the expensive half of this audit, and it is quadratic in the
/// operations checked.
fn lean_source(exempt: &[(&str, &str)], out: &Path) -> String {
    let exempt_literal = exempt
        .iter()
        .map(|(name, _)| format!("`{name}"))
        .collect::<Vec<_>>()
        .join(", ");
    let out_literal = lean_string_literal(&out.to_string_lossy());
    format!(
        r#"import Lean
import Grass.Std.Logical.Vec
import Grass.Std.Logical.Order

open Lean

namespace GrassToolsCoverageAudit

/-- The observations decision 6 is phrased over. -/
def lengthName : Name := `Grass.Std.Logical.Vec.length

/-- The checked accessor. -/
def getName : Name := `Grass.Std.Logical.Vec.get?

/-- Exempt by clause (ii) or the alias clause; the reasons live with the caller. -/
def exempt : List Name := [{exempt_literal}]

/-- Whether `e` contains `obs` applied to a term headed by `op`. -/
partial def observes (obs op : Name) (e : Expr) : Bool :=
  let here :=
    e.getAppFn.constName? == some obs &&
      e.getAppArgs.any fun arg => arg.getAppFn.constName? == some op
  here || match e with
    | .app f a => observes obs op f || observes obs op a
    | .lam _ t b _ => observes obs op t || observes obs op b
    | .forallE _ t b _ => observes obs op t || observes obs op b
    | .letE _ t v b _ => observes obs op t || observes obs op v || observes obs op b
    | .mdata _ b => observes obs op b
    | .proj _ _ b => observes obs op b
    | _ => false

/-- Whether `op` appears anywhere in `e`. -/
partial def mentions (op : Name) (e : Expr) : Bool :=
  e.getAppFn.constName? == some op || match e with
    | .app f a => mentions op f || mentions op a
    | .lam _ t b _ => mentions op t || mentions op b
    | .forallE _ t b _ => mentions op t || mentions op b
    | .letE _ t v b _ => mentions op t || mentions op v || mentions op b
    | .mdata _ b => mentions op b
    | .proj _ _ b => mentions op b
    | _ => false

/--
Whether `e` contains an equation observing `op` on one side whose *other* side
does not mention `op`.

This is the non-vacuity condition, and it exists because the audit without it was
fooled by exactly the attack adversarial review used against the prose rule. A
probe operation carrying

    @[simp] theorem length_probe (v) (i) : (probe v i).length = (probe v i).length := rfl

compiles, is wrong, and satisfied "a law computing its length" -- the audit
counted it and reported success. Requiring the other side to be free of `op` is
what makes a law say something about the operation rather than about itself, and
it is the mechanical form of decision 6's "neither may be `f`'s own definitional
body".
-/
partial def observesNonVacuously (obs op : Name) (e : Expr) : Bool :=
  let hereEq :=
    if e.getAppFn.constName? == some ``Eq then
      match e.getAppArgs.toList with
      | [_, lhs, rhs] =>
        (observes obs op lhs && !mentions op rhs) ||
          (observes obs op rhs && !mentions op lhs)
      | _ => false
    else false
  hereEq || match e with
    | .app f a => observesNonVacuously obs op f || observesNonVacuously obs op a
    | .lam _ t b _ => observesNonVacuously obs op t || observesNonVacuously obs op b
    | .forallE _ t b _ => observesNonVacuously obs op t || observesNonVacuously obs op b
    | .letE _ t v b _ =>
      observesNonVacuously obs op t || observesNonVacuously obs op v ||
        observesNonVacuously obs op b
    | .mdata _ b => observesNonVacuously obs op b
    | .proj _ _ b => observesNonVacuously obs op b
    | _ => false

/-- Whether a constant's result type is a `Vec`. -/
partial def returnsVec (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => returnsVec b
  | _ => e.getAppFn.constName? == some `Grass.Std.Logical.Vec

end GrassToolsCoverageAudit

open GrassToolsCoverageAudit in
run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  let vecNs := `Grass.Std.Logical.Vec

  -- Every def in the Vec namespace, split by whether the bar reaches it.
  let mut ops : Array Name := #[]
  let mut exempted : Array Name := #[]
  let mut outsideBar : Array Name := #[]
  for (name, info) in env.constants.toList do
    unless vecNs.isPrefixOf name && !name.isInternal do continue
    match info with
    | .defnInfo d =>
      if returnsVec d.type then
        if exempt.contains name then exempted := exempted.push name
        else ops := ops.push name
      else outsideBar := outsideBar.push name
    | _ => pure ()

  -- Collect every theorem statement once.
  let mut theorems : Array Expr := #[]
  for (_, info) in env.constants.toList do
    match info with
    | .thmInfo t => theorems := theorems.push t.type
    | _ => pure ()

  let mut lines : Array String := #[]
  for op in ops do
    let hasLength := theorems.any fun t => observesNonVacuously lengthName op t
    let hasGet := theorems.any fun t => observesNonVacuously getName op t
    let bit (b : Bool) : String := if b then "1" else "0"
    lines := lines.push ("O\t" ++ toString op ++ "\t" ++ bit hasLength ++ "\t" ++ bit hasGet)
  for name in exempted do
    lines := lines.push ("A\t" ++ toString name)
  for name in outsideBar do
    lines := lines.push ("X\t" ++ toString name)
  lines := lines.push ("T\t" ++ toString theorems.size)
  lines := lines.push
    ("Z\t" ++ toString ops.size ++ "\t" ++ toString exempted.size ++ "\t"
      ++ toString outsideBar.size)
  IO.FS.writeFile {out_literal} (String.intercalate "\n" lines.toList ++ "\n")
"#
    )
}

// ---------------------------------------------------------------------------
// Running it.
// ---------------------------------------------------------------------------

/// Elaborate the generated source under the repository's toolchain and read back
/// the records.
///
/// `lake env lean` is how `.github/workflows/library.yml` invoked
/// `Tools/CoverageAudit.lean`, and it is what puts the built `.olean` files on
/// `LEAN_PATH`; the working directory therefore has to be the repository root,
/// exactly as it did before.
///
/// The record set goes to a file rather than to standard output so that a Lean
/// diagnostic can never be mistaken for a record, and a record can never be
/// mistaken for a diagnostic.
fn elaborate(build_source: impl FnOnce(&Path) -> String) -> Result<String, String> {
    let dir = tempfile::Builder::new()
        .prefix("grass-coverage-audit")
        .tempdir()
        .map_err(|err| {
            format!("observation-coverage audit: could not create a working directory: {err}")
        })?;
    let script: PathBuf = dir.path().join("CoverageAuditProbe.lean");
    let records: PathBuf = dir.path().join("records.tsv");
    fs::write(&script, build_source(&records)).map_err(|err| {
        format!(
            "observation-coverage audit: could not write {}: {err}",
            script.display()
        )
    })?;

    let output = Command::new("lake")
        .args(["env", "lean"])
        .arg(&script)
        .output()
        .map_err(|err| {
            format!(
                "observation-coverage audit: could not run `lake env lean`: {err}\nThis audit \
                 needs the pinned toolchain and must be run from the repository root."
            )
        })?;
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    if !output.status.success() {
        return Err(format!(
            "observation-coverage audit: the Lean side of the audit failed, so nothing was \
             audited:\n{stdout}{stderr}"
        ));
    }
    fs::read_to_string(&records).map_err(|err| {
        format!(
            "observation-coverage audit: the Lean side produced no record set ({err}), so nothing \
             was audited:\n{stdout}{stderr}"
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
    let records = elaborate(|out| lean_source(RECURSION_OR_ALIAS, out))?;
    verdict(&parse_records(&records)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn op(name: &str, length: bool, get: bool) -> Operation {
        Operation {
            name: name.to_string(),
            has_length_law: length,
            has_get_law: get,
        }
    }

    /// A report whose exemption set is the full list, so that only the argument
    /// under test differs from a clean run.
    fn report(checked: Vec<Operation>, outside: usize) -> Report {
        Report {
            checked,
            exempted: RECURSION_OR_ALIAS
                .iter()
                .map(|(name, _)| (*name).to_string())
                .collect(),
            outside_bar: (0..outside).map(|i| format!("Grass.X.f{i}")).collect(),
            theorems: 400,
        }
    }

    // --- the verdict ------------------------------------------------------

    #[test]
    fn an_operation_with_both_laws_passes_and_the_line_counts_what_was_seen() {
        let r = report(
            vec![
                op("Grass.Std.Logical.Vec.map", true, true),
                op("Grass.Std.Logical.Vec.take", true, true),
            ],
            44,
        );
        assert_eq!(
            verdict(&r).expect("clean"),
            "observation-coverage audit: 2 Vec-returning operations each carry a length law and a \
             get? law; 9 exempt by clause (ii) or the alias clause; 44 declarations outside the \
             bar's reach"
        );
    }

    #[test]
    fn each_shortfall_is_reported_in_its_own_words() {
        assert_eq!(shortfall(&op("f", true, true)), None);
        assert_eq!(
            shortfall(&op("f", false, false)),
            Some("no length law and no get? law")
        );
        assert_eq!(
            shortfall(&op("f", false, true)),
            Some("no law computing its length")
        );
        assert_eq!(
            shortfall(&op("f", true, false)),
            Some("no law computing its get?")
        );
    }

    #[test]
    fn a_missing_law_fails_and_names_the_operation() {
        // `Vec.sum` and `Vec.count` shipped in the commit that stated the rule.
        let r = report(
            vec![
                op("Grass.Std.Logical.Vec.map", true, true),
                op("Grass.Std.Logical.Vec.sum", false, false),
                op("Grass.Std.Logical.Vec.reverse", true, false),
            ],
            44,
        );
        let message = verdict(&r).expect_err("a missing law must fail the gate");
        assert!(
            message.starts_with(
                "observation-coverage audit failed; docs/STDLIB_IMPLEMENTATION_PLAN.md decision 6 \
                 requires a length law and a get? law for every Vec-returning operation:"
            ),
            "{message}"
        );
        assert!(
            message.contains("  Grass.Std.Logical.Vec.sum: no length law and no get? law"),
            "{message}"
        );
        assert!(
            message.contains("  Grass.Std.Logical.Vec.reverse: no law computing its get?"),
            "{message}"
        );
        assert!(!message.contains("Vec.map"), "{message}");
    }

    #[test]
    fn a_vacuous_self_law_is_not_a_law_the_report_can_see() {
        // The attack that broke the first version reaches this code as
        // `has_length_law: false`, because `observesNonVacuously` refuses it in
        // Lean. What is checked here is that the Rust half does not re-admit it by
        // treating "an operation the search ran over" as "an operation with a law".
        let r = report(vec![op("Grass.Std.Logical.Vec.probe", false, false)], 0);
        assert!(verdict(&r).is_err());
    }

    // --- the vacuous-pass refusal ----------------------------------------

    #[test]
    fn audit_of_zero_operations_is_refused() {
        // The failure this port exists to close. `missing` is empty, so
        // `Tools/CoverageAudit.lean` would have printed "0 Vec-returning operations
        // each carry a length law and a get? law" and exited 0.
        let message = verdict(&Report::default())
            .expect_err("an audit that examined nothing must not report success");
        assert!(message.contains("audited nothing"), "{message}");
        assert!(
            message.contains("Refusing to report clean observation coverage"),
            "{message}"
        );
        assert!(
            !message.contains("each carry a length law"),
            "an empty scan must never borrow the success line: {message}"
        );
    }

    #[test]
    fn an_empty_theorem_set_is_refused_rather_than_blamed_on_the_library() {
        let mut r = report(vec![op("Grass.Std.Logical.Vec.map", false, false)], 0);
        r.theorems = 0;
        let message = verdict(&r).expect_err("no theorems means no audit");
        assert!(
            message.contains("no theorem statements were scanned"),
            "{message}"
        );
    }

    // --- stale exemptions -------------------------------------------------

    #[test]
    fn an_exemption_that_matches_nothing_is_noted_without_changing_the_verdict() {
        // This is the shape of what the tool reports on the real tree: `splitAt`
        // returns a pair, so the bar never reached it and the clause (ii) reason
        // beside it excuses nothing.
        let mut r = report(vec![op("Grass.Std.Logical.Vec.map", true, true)], 44);
        r.exempted.remove("Grass.Std.Logical.Vec.splitAt");
        let line = verdict(&r).expect("an inert exemption is a note, not a finding");
        assert!(
            line.contains(
                "1 of the 9 exemptions name nothing this audit would otherwise have \
                           checked"
            ),
            "{line}"
        );
        assert!(line.contains("  Grass.Std.Logical.Vec.splitAt"), "{line}");
        // The count in the headline is still the list's length, as it was.
        assert!(
            line.contains("9 exempt by clause (ii) or the alias clause"),
            "{line}"
        );
    }

    #[test]
    fn a_fully_matched_exemption_list_adds_no_note() {
        let r = report(vec![op("Grass.Std.Logical.Vec.map", true, true)], 44);
        assert!(stale_exemptions(&r).is_empty());
        assert!(!verdict(&r).expect("clean").contains("note:"));
    }

    // --- the record format ------------------------------------------------

    #[test]
    fn records_parse_into_the_report_they_describe() {
        let text = "O\tGrass.Std.Logical.Vec.map\t1\t1\nO\tGrass.Std.Logical.Vec.sum\t0\t0\n\
                    A\tGrass.Std.Logical.Vec.foldl\nX\tGrass.Std.Logical.Vec.isEmpty\n\
                    T\t412\nZ\t2\t1\t1\n";
        let parsed = parse_records(text).expect("well-formed");
        assert_eq!(parsed.checked.len(), 2);
        assert!(parsed.checked[0].has_length_law && parsed.checked[0].has_get_law);
        assert!(!parsed.checked[1].has_length_law && !parsed.checked[1].has_get_law);
        assert_eq!(parsed.exempted.len(), 1);
        assert_eq!(parsed.outside_bar, vec!["Grass.Std.Logical.Vec.isEmpty"]);
        assert_eq!(parsed.theorems, 412);
    }

    #[test]
    fn a_truncated_record_set_is_refused_rather_than_audited() {
        let short = "O\tGrass.Std.Logical.Vec.map\t1\t1\nT\t412\n";
        let message = parse_records(short).expect_err("a set with no terminator must be refused");
        assert!(message.contains("no terminator"), "{message}");

        let disagreeing = "O\tGrass.Std.Logical.Vec.map\t1\t1\nT\t412\nZ\t9\t0\t0\n";
        let message = parse_records(disagreeing).expect_err("a disagreeing count must be refused");
        assert!(message.contains("truncated in transit"), "{message}");
    }

    #[test]
    fn an_unrecognised_record_is_refused() {
        assert!(parse_records("hello\nZ\t0\t0\t0\n").is_err());
        assert!(parse_records("O\tf\t2\t1\nZ\t1\t0\t0\n").is_err());
        assert!(parse_records("Z\t0\t0\t0\nT\t1\n").is_err());
    }

    // --- generation -------------------------------------------------------

    #[test]
    fn the_generated_source_bakes_in_the_exemption_list_and_the_two_imports() {
        let source = lean_source(RECURSION_OR_ALIAS, Path::new("out.tsv"));
        for (name, _) in RECURSION_OR_ALIAS {
            assert!(source.contains(&format!("`{name}")), "{name}");
        }
        // Widening the import set would admit laws from further away and weaken
        // the audit, so the two the Lean file carried are the two here.
        assert_eq!(source.matches("\nimport Grass.").count(), 2);
        assert!(source.contains("import Grass.Std.Logical.Vec\n"));
        assert!(source.contains("import Grass.Std.Logical.Order\n"));
        assert!(source.contains("observesNonVacuously"));
    }

    #[test]
    fn a_windows_path_survives_becoming_a_lean_literal() {
        assert_eq!(
            lean_string_literal(r"C:\tmp\records.tsv"),
            "\"C:\\\\tmp\\\\records.tsv\""
        );
    }
}
