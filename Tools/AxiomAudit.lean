import Lean
import Grass.Core.Context
import Grass.Core.Generational
import Grass.Core.Name
import Grass.Core.Uid
import Grass.Memory.Access
import Grass.Memory.AddressSpace
import Grass.Memory.Audit
import Grass.Memory.Authority
import Grass.Memory.Event
import Grass.Memory.Fault
import Grass.Memory.Ordering
import Grass.Memory.Profile
import Grass.Memory.Provenance
import Grass.Memory.Range
import Grass.Memory.Rights
import Grass.Memory.State
import Grass.Memory.Substep
import Grass.Obligation.Core
import Grass.Obligation.Delta
import Grass.Obligation.Disposition
import Grass.Op.Facets
import Grass.Op.Step
import Grass.Resource.Algebra
import Grass.Resource.Axis
import Grass.Std.Logical.Byte
import Grass.Std.Logical.FiniteMap
import Grass.Std.Logical.Vec

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

## Coverage is checked, not assumed

An explicit import list is a coverage hazard, and it failed in exactly the
predictable way: within a day of being written it had fallen six modules behind
the tree, and a maximally false axiom in an unimported module passed both this
tool and `lake build` with exit 0. A gate that silently stops covering the newest
code is worse than no gate, because the green run still reads as assurance.

`checkCoverage` therefore walks `Grass/` on disk and fails if any module found
there is absent from the imported environment. The import list is still written
out below — Lean has no dynamic import — but it can no longer be wrong without
the build saying so.

The list also means this file imports every leaf, which
`docs/OLEAN_SHARDING.md` §2 forbids for an aggregate certificate. That rule is
about proof aggregates whose types grow with their descendants. This is a
diagnostic that must see everything by construction, produces no theorem, and is
not on the path to `VerifiedProgram`. It lives under `Tools/` and outside the
library glob so it cannot be mistaken for one.

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

/-- Whether a declaration belongs to the audited namespace. -/
def isAudited (name : Name) : Bool :=
  (`Grass).isPrefixOf name && !name.isInternal

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

open Grass.Tools in
run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  -- Coverage first: an axiom audit over half the tree is not an axiom audit.
  let imported := env.header.moduleNames
  let onDisk ← Grass.Tools.modulesOnDisk (System.FilePath.mk "Grass") `Grass
  let missing := onDisk.filter fun m => !imported.contains m
  unless missing.isEmpty do
    throwError m!"axiom audit coverage gap: these modules exist under Grass/ but are not imported by Tools/AxiomAudit.lean, so their declarations were never scanned:
{MessageData.joinSep (missing.toList.map (m!"  {·}")) "
"}"
  let mut audited : Nat := 0
  let mut unsafeFindings : Array Name := #[]
  let mut findings : Array (Name × Name) := #[]
  for (name, info) in env.constants.toList do
    unless isAudited name do continue
    audited := audited + 1
    -- §3 also names "unsafe declarations used as proof".
    if info.isUnsafe then
      unsafeFindings := unsafeFindings.push name
    let axioms ← Elab.Command.liftCoreM (collectAxioms name)
    for used in axioms do
      unless allowedAxioms.contains used do
        findings := findings.push (name, used)
  unless unsafeFindings.isEmpty do
    throwError m!"axiom audit failed; docs/FOUNDATION.md section 3 forbids unsafe declarations used as proof:
{MessageData.joinSep (unsafeFindings.toList.map (m!"  {·}")) "
"}"
  if findings.isEmpty then
    logInfo m!"axiom audit: {audited} Grass declarations across {onDisk.size} modules, no axiom outside the allowlist, no unsafe declaration"
  else
    let lines := findings.map fun (name, used) => m!"  {name} depends on {used}"
    throwError m!"axiom audit failed; docs/FOUNDATION.md section 3 permits only \
{allowedAxioms}\n{MessageData.joinSep lines.toList "\n"}"
