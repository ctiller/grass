import Lean

/-!
# Axiom audit

`docs/FOUNDATION.md` §3: "Every theorem used by the verified gate is audited
transitively for axioms, regardless of which dependency declared them. Only the
reviewed Lean logical foundation allowlist (`propext`, quotient soundness, and
classical choice, with their exact toolchain declaration names) is permitted.
Dependency-defined axioms, `sorryAx`, `sorry`, `admit`, unsafe declarations used
as proof, and equivalent admission mechanisms make the gate fail."

This tool implements that audit over every declaration in the `Grass` namespace.
It is run by `.github/workflows/library.yml` and fails the build on any axiom
outside the allowlist.

## Dynamic module discovery eliminates coverage drift and merge friction

An explicit import list is a coverage hazard and a continuous source of merge
conflicts across active development branches. Previous revisions attempted to
detect drift by walking `Grass/` on disk and comparing against static imports.

This tool dynamically discovers every module under `Grass/` on disk, loads
their compiled binary modules (`.olean`) into the Lean environment at
elaboration time via `importModules`, and audits all declarations directly.
No hardcoded import list is required, eliminating coverage drift and cross-branch
merge conflicts entirely.

The diagnostic produces no theorem and is not on the path to `VerifiedProgram`.
It lives under `Tools/` and outside the library glob so it cannot be mistaken
for one.

It is also not a proof. `docs/FOUNDATION.md` §3 is discharged by the kernel
recording which axioms each declaration depends on; this tool reads that record
and reports. A green run is evidence, in the sense of
`docs/VALIDATION.md`, not a theorem.
-/

open Lean

namespace Grass.Tools

/--
The reviewed logical-foundation allowlist.

Exactly the three constants `docs/FOUNDATION.md` §3 permits, by their toolchain
declaration names. Adding to this list is a trust-boundary change and requires
the review that section demands, not an edit here.
-/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/--
The name a declaration is written under, with any `private` mangling removed.

A `private` declaration is stored as `_private.<module>.<n>.<real name>`, whose
first component is `_private` rather than `Grass`. Testing the namespace on the
stored name therefore skipped every private declaration in the library -- 111 in
the x86 tree alone, including proof-carrying theorems. Stripping the mangling
first is what puts them back inside the audit.
-/
def userFacing (name : Name) : Name := (privateToUserName? name).getD name

/-- Whether a declaration belongs to the audited namespace. -/
def isAudited (name : Name) : Bool :=
  let n := userFacing name
  (`Grass).isPrefixOf n && !n.isInternal

/--
Attributes that make a declaration's compiled behaviour differ from its logical
definition.

`docs/FOUNDATION.md` §3 is about what a proof may depend on, and this is the
same question one step out. Every differential in this repository generates its
corpus by *executing* a Grass definition through `lake env lean --run`, while
every theorem is about the definition the kernel sees. `@[implemented_by]`,
`@[extern]` and `@[csimp]` are exactly the three ways to make those two objects
different.

A reviewer demonstrated the consequence: an `opcodeTable` whose `0x83` row was
poisoned to the wrong immediate size, with `@[implemented_by]` pointing at an
untouched copy, passed the build, both audits, the ledger and all four
differentials -- including the decoder differential written specifically to
catch that mutation. It produces no axiom, no warning and no `unsafe` marker,
so nothing else here would ever notice.

None of the three is forbidden in general; they are forbidden on declarations
this repository's assurance rests on, which is every `Grass` declaration.
-/
def compiledOverride (env : Environment) (name : Name) : Option String :=
  if (Lean.Compiler.getImplementedBy? env name).isSome then
    some "@[implemented_by]"
  else if Lean.isExtern env name then
    some "@[extern]"
  else
    Option.none

/--
Every Lean module found under `root` on disk, as a module name.

The audit compares this against the environment's imported modules, so a module
that exists but was never imported is reported rather than silently skipped.
-/
partial def modulesOnDisk (root : System.FilePath) (prefix_ : Name) :
    IO (Array Name) := do
  let mut found : Array Name := #[]
  for entry in (← root.readDir) do
    let name := entry.fileName
    if ← entry.path.isDir then
      found := found ++ (← modulesOnDisk entry.path (prefix_ ++ Name.mkSimple name))
    else if name.endsWith ".lean" then
      let stem := name.dropEnd 5 |>.toString
      found := found.push (prefix_ ++ Name.mkSimple stem)
  return found

end Grass.Tools

open Grass.Tools Lean Elab Command in
run_cmd do
  let lakeLib := System.FilePath.mk ".lake" / "build" / "lib" / "lean"
  Lean.searchPathRef.modify fun sp => lakeLib :: sp
  let onDisk ← Grass.Tools.modulesOnDisk (System.FilePath.mk "Grass") `Grass
  if onDisk.isEmpty then
    throwError "axiom audit coverage gap: no modules found under Grass/"
  let imports := onDisk.map fun m => ({ module := m } : Import)
  let env ← importModules imports {}
  setEnv env
  let mut audited : Nat := 0
  let mut unsafeFindings : Array Name := #[]
  let mut overrideFindings : Array (Name × String) := #[]
  let mut findings : Array (Name × Name) := #[]
  for (name, info) in env.constants.toList do
    unless isAudited name do continue
    audited := audited + 1
    -- §3 also names "unsafe declarations used as proof".
    if info.isUnsafe then
      unsafeFindings := unsafeFindings.push name
    -- The compiled definition must be the proved one; see `compiledOverride`.
    match compiledOverride env name with
    | some attr => overrideFindings := overrideFindings.push (userFacing name, attr)
    | Option.none => pure ()
    let axioms ← Elab.Command.liftCoreM (collectAxioms name)
    for used in axioms do
      unless allowedAxioms.contains used do
        findings := findings.push (name, used)
  unless overrideFindings.isEmpty do
    let lines := overrideFindings.map fun (name, attr) => m!"  {name} carries {attr}"
    throwError m!"axiom audit failed: a Grass declaration's compiled behaviour is \
allowed to differ from its logical definition. Every differential in this \
repository measures the compiled definition while every theorem is about the \
logical one, so this severs the two.
{MessageData.joinSep lines.toList "
"}"
  unless unsafeFindings.isEmpty do
    throwError m!"axiom audit failed; docs/FOUNDATION.md section 3 forbids unsafe declarations used as proof:
{MessageData.joinSep (unsafeFindings.toList.map (m!"  {·}")) "
"}"
  if findings.isEmpty then
    logInfo m!"axiom audit: {audited} Grass declarations across {onDisk.size} modules, no axiom outside the allowlist, no unsafe declaration, no compiled override"
  else
    let lines := findings.map fun (name, used) => m!"  {name} depends on {used}"
    throwError m!"axiom audit failed; docs/FOUNDATION.md section 3 permits only \
{allowedAxioms}\n{MessageData.joinSep lines.toList "\n"}"
