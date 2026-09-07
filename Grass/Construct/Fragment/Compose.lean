import Grass.Construct.Fragment.Verified

/-!
# Verified fragment sequencing

Composition consumes explicit laws for sequential execution and effect
derivation.  It also requires a logical boundary proof from the first
fragment's exact exit classification to the second fragment's entry condition.
No instruction semantics or effect algebra is guessed by this layer.
-/

namespace Grass.Construct.Fragment

open Grass.CFG

universe u v w

/-- Laws an operation/profile pair supplies for sequential fragment closure. -/
structure SequentialLaws {Instruction : Type u} {State : Type v} {Effect : Type w}
    (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  combine : Effect → Effect → Effect
  executes_append : ∀ left right before after,
    semantics.Executes (left ++ right) before after ↔
      ∃ middle,
        semantics.Executes left before middle ∧
        semantics.Executes right middle after
  effects_append : ∀ left right,
    effectModel.derive (left ++ right) =
      combine (effectModel.derive left) (effectModel.derive right)

/-- Sequential contract: enter through the first contract and expose exactly
the second contract's exit family. -/
def thenContract {State : Type v}
    (first second : BlockContract State) : BlockContract State where
  requires := first.requires
  exits := second.exits

/-- Every uniquely classified first-fragment result establishes the next entry
condition. -/
def BoundaryCompatible {State : Type v}
    (first second : BlockContract State) : Prop :=
  ∀ state, ClassifiesExactlyOneExit first state → second.requires state

namespace VerifiedFragment

variable {Instruction : Type u} {State : Type v} {Effect : Type w}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {firstContract secondContract : BlockContract State}

/-- Compose two locally verified fragments using explicit semantic, effect, and
contract-boundary laws. -/
def compose
    (laws : SequentialLaws semantics effectModel)
    (first : VerifiedFragment semantics effectModel firstContract)
    (second : VerifiedFragment semantics effectModel secondContract)
    (boundary : BoundaryCompatible firstContract secondContract) :
    VerifiedFragment semantics effectModel (thenContract firstContract secondContract) where
  source := .sequence [first.source, second.source]
  contractWellFormed := by
    rw [BlockContract.wellFormed_iff]
    simpa [thenContract, BlockContract.exitTags] using
      (BlockContract.wellFormed_iff secondContract).mp second.contractWellFormed
  effects := laws.combine first.effects second.effects
  effectsExact := by
    calc
      laws.combine first.effects second.effects =
          laws.combine (effectModel.derive first.source.expand)
            (effectModel.derive second.source.expand) := by
              rw [first.effectsExact, second.effectsExact]
      _ = effectModel.derive (first.source.expand ++ second.source.expand) :=
        (laws.effects_append first.source.expand second.source.expand).symm
      _ = effectModel.derive
          (Source.sequence [first.source, second.source]).expand := by simp
  localCorrect := by
    intro before after hrequires hexecutes
    have happend : semantics.Executes
        (first.source.expand ++ second.source.expand) before after := by
      simpa using hexecutes
    obtain ⟨middle, hfirst, hsecond⟩ :=
      (laws.executes_append first.source.expand second.source.expand before after).mp happend
    have firstExit := first.localCorrect before middle hrequires hfirst
    exact second.localCorrect middle after (boundary middle firstExit) hsecond

@[simp] theorem compose_source_expand
    (laws : SequentialLaws semantics effectModel)
    (first : VerifiedFragment semantics effectModel firstContract)
    (second : VerifiedFragment semantics effectModel secondContract)
    (boundary : BoundaryCompatible firstContract secondContract) :
    (first.compose laws second boundary).source.expand =
      first.source.expand ++ second.source.expand := by
  simp [compose]

end VerifiedFragment

end Grass.Construct.Fragment
