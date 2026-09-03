import Lean.Elab.Command
import Grass.ISA.X86.Profile
import Tests.ISA.X86.Spike1Addressing

/-!
# Axiom audit gate for the x86 trees

`docs/DECISIONS.md` 31: "Verified theorems receive a transitive axiom audit
across all dependencies; only exact reviewed Lean logical-foundation constants
are allowed." `docs/VALIDATION.md` §6 requires each profile to publish "a
transitive axiom report for every verified theorem, regardless of declaration
origin" and "rejection of every dependency-defined axiom, `sorryAx`, or
equivalent admission constant".

This file is that audit, run at build time. It walks every theorem in the
modules this agent owns and fails the build if one depends on anything outside
the allowlist.

## Why it is a gate and not a report

The audit found a real violation the day it was first run. Two theorems proved
with `bv_decide` carried a generated axiom:

```text
axiom writeBack.w16_preserves_high._native.bv_decide.ax_1_5 :
  Std.Tactic.BVDecide.Reflect.verifyBVExpr _expr _cert = true
```

`bv_decide` had run its LRAT checker natively and admitted the answer, which is
`native_decide` in another costume — prohibited by `docs/DECISIONS.md` 23, whose
same clause permits `bv_decide`. Four sibling theorems using the identical
tactic were kernel-checked and clean, because their goals closed in the
normalizer before the solver was called.

That is the case a report does not catch. Nothing in the source distinguishes
the two paths; the tactic is spelled the same way, the proof succeeds either
way, and a reviewer reading the file sees no difference. Only running the audit
tells them apart, so it runs on every build.

Both theorems were reproved without the tactic. See
`Grass/ISA/X86/Register.lean`.

## Scope

`Grass.ISA.X86.*`, `Grass.Cite.*` and this test namespace — the modules under
`Grass/ISA/X86/**` and the citation vocabulary held in custody there.

It deliberately does not audit the whole repository. Other agents own their
trees, and a gate that failed their builds from this file would be this agent
legislating for them. The mechanism generalizes by changing one list, and should
be lifted to a repository-wide check by whoever owns the CI ratchet in
`docs/VALIDATION.md` §7.

## The allowlist

`propext`, `Classical.choice` and `Quot.sound`: the three axioms of Lean's own
logical foundation. Nothing else, and in particular not `sorryAx`, not
`Lean.ofReduceBool`, and not a tactic's generated certificate.
-/

namespace Grass.Tests.ISA.X86.AxiomAudit

open Lean Elab Command

/-- The reviewed Lean logical-foundation constants. -/
private def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Namespaces this gate is responsible for. -/
private def auditedPrefixes : List String :=
  ["Grass.ISA.X86.", "Grass.Cite.", "Grass.Tests.ISA.X86."]

private def isAudited (n : Name) : Bool :=
  auditedPrefixes.any (fun p => String.startsWith n.toString p)

run_cmd do
  let env ← getEnv
  let mut audited : Nat := 0
  let mut violations : Nat := 0
  for (nm, ci) in env.constants.toList do
    if isAudited nm then
      match ci with
      | .thmInfo _ =>
        audited := audited + 1
        let axs ← liftCoreM <| Lean.collectAxioms nm
        for ax in axs do
          if !(allowedAxioms.contains ax) then
            violations := violations + 1
            logError m!"{nm} depends on the disallowed axiom {ax}"
      | _ => pure ()
  if violations == 0 then
    logInfo m!"axiom audit: {audited} theorems, all within the reviewed allowlist"

end Grass.Tests.ISA.X86.AxiomAudit
