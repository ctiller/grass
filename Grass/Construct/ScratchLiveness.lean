import Grass.Construct.Scratch

/-!
# Scratch selection tied to machine liveness

`CheckedScratchContext` connects an exact `CheckedScratch` selection to a
machine-supplied liveness relation at every state satisfying the fragment entry
contract. Construction does not derive that relation. `withLiveScratch` merely
feeds the proved selection to the fixed-contract binder, retaining exact body
source and the machine owner's local-correctness proof.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- Machine-owned statement of register liveness at one semantic state. -/
structure ScratchLivenessModel (Register : Type u) (State : Type v) where
  Live : State → Register → Prop

/--
A checked scratch selection whose supplied live set is exact at contract entry.

The equivalence is pointwise rather than one-way: omitting a genuinely live
register and conservatively retaining a dead register both fail exactness.
-/
structure CheckedScratchContext {Register : Type u} [DecidableEq Register]
    {State : Type v} (model : ScratchLivenessModel Register State)
    (contract : BlockContract State) (request : ScratchRequest Register) where
  selection : CheckedScratch request
  liveExact : ∀ state, contract.requires state → ∀ register,
    model.Live state register ↔ register ∈ request.live

namespace CheckedScratchContext

variable {Register : Type u} [DecidableEq Register]
  {State : Type v} {model : ScratchLivenessModel Register State}
  {contract : BlockContract State} {request : ScratchRequest Register}

/-- The selected scratch register is not live in any admitted entry state. -/
theorem selectedNotLive (context : CheckedScratchContext model contract request)
    {state : State} (entry : contract.requires state) :
    ¬model.Live state context.selection.register := by
  intro live
  exact context.selection.notLive (context.liveExact state entry _ |>.mp live)

end CheckedScratchContext

/--
Run a verified body using a selection proved non-live at its exact entry contract.

`withLiveScratch` delegates definitionally to `withSelectedScratch`; it does not
add source, synthesize liveness, or weaken the body's fixed contract.
-/
def withLiveScratch {Register : Type u} [DecidableEq Register]
    {Instruction : Type w} {State : Type v} {Effect : Type x}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {contract : BlockContract State} {request : ScratchRequest Register}
    {model : ScratchLivenessModel Register State}
    (context : CheckedScratchContext model contract request)
    (body : ScratchHandle context.selection →
      VerifiedFragment semantics effectModel contract) :
    VerifiedFragment semantics effectModel contract :=
  withSelectedScratch context.selection body

/-- `withLiveScratch_source` exposes the exact selected body source unchanged. -/
@[simp] theorem withLiveScratch_source
    {Register : Type u} [DecidableEq Register]
    {Instruction : Type w} {State : Type v} {Effect : Type x}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {contract : BlockContract State} {request : ScratchRequest Register}
    {model : ScratchLivenessModel Register State}
    (context : CheckedScratchContext model contract request)
    (body : ScratchHandle context.selection →
      VerifiedFragment semantics effectModel contract) :
    (withLiveScratch context body).source =
      (body context.selection.handle).source :=
  rfl

end Grass.Construct
