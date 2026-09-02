import Lean
import Grass.Core.Context
import Grass.Core.Generational
import Grass.Core.Name
import Grass.Core.Uid
import Grass.Memory.Access
import Grass.Memory.AddressSpace
import Grass.Memory.Audit
import Grass.Memory.Event
import Grass.Memory.Facet
import Grass.Memory.Fault
import Grass.Memory.Ordering
import Grass.Memory.Profile
import Grass.Memory.Provenance
import Grass.Memory.Range
import Grass.Memory.Rights
import Grass.Memory.Substep
import Grass.Obligation.Core
import Grass.Obligation.Delta
import Grass.Obligation.Disposition
import Grass.Resource.Algebra
import Grass.Resource.Axis
import Grass.Std.Logical.Byte
import Grass.Std.Logical.FiniteMap

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

Two notes on why it is a separate tool rather than a library module.

It carries an explicit import list naming every module, which
`docs/OLEAN_SHARDING.md` §2 forbids for an aggregate certificate — "no aggregate
imports every leaf directly". That rule is about proof aggregates whose types
would grow with their descendants. This is a diagnostic that must see everything
by construction, produces no theorem, and is not on the path to
`VerifiedProgram`. It lives under `Tools/` and outside the library glob so it
cannot be mistaken for one.

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

end Grass.Tools

open Grass.Tools in
run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  let mut audited : Nat := 0
  let mut findings : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    unless isAudited name do continue
    audited := audited + 1
    let axioms ← Elab.Command.liftCoreM (collectAxioms name)
    for used in axioms do
      unless allowedAxioms.contains used do
        findings := findings.push (name, used)
  if findings.isEmpty then
    logInfo m!"axiom audit: {audited} Grass declarations, no axiom outside the allowlist"
  else
    let lines := findings.map fun (name, used) => m!"  {name} depends on {used}"
    throwError m!"axiom audit failed; docs/FOUNDATION.md section 3 permits only \
{allowedAxioms}\n{MessageData.joinSep lines.toList "\n"}"
