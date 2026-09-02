import Grass.Core.Name
import Grass.Memory.Access

/-!
# Substeps and the commit-prefix model

`docs/MEMORY_MODEL.md` §1: "multi-access instructions and APIs are represented by
ordered substeps or an explicit commit-prefix model, and their profiles state
which earlier completed effects remain visible when a later substep faults,
interrupts, or completes partially. Grass must not silently assume that a whole
instruction is transactional."

There are two independent granularities of partiality and conflating them loses
information.

*Within* one access, `AccessStatus` carries how many bytes committed. A store
that faults halfway across a page boundary is one access with a committed prefix.

*Across* accesses, a `SubstepSequence` says what survives when a later substep
fails. `rep movsb` is not one access with a byte count; it is a sequence whose
earlier iterations completed and stay completed.

`onFault` has **no default value**. `docs/INSTRUCTIONS.md` §4 says a macro "is not
semantically atomic unless a target theorem proves that property", and the same
holds for an instruction. An author who omits the declaration gets a missing-field
error, not an assumption of atomicity. `transactional` additionally carries the
name of the justification that establishes it, so claiming atomicity leaves a
citation trail rather than being free.
-/

namespace Grass.Memory

open Grass.Core

/--
What remains visible when a substep of a sequence fails.

There is deliberately no "unspecified" case. `docs/FOUNDATION.md` law 8 requires
unknown effects to be rejected rather than approximated, and the effect of a
failure partway through a multi-access instruction is exactly the kind of thing
a permissive default would get wrong in the safe-looking direction.
-/
inductive FaultVisibility where
  /-- Substeps that completed before the failure remain visible. This is the
  default *behavior* of most hardware, though not a default *value* here. -/
  | priorEffectsVisible
  /-- No substep is visible unless all are. Requires a target theorem, named by
  `justification`, per `docs/INSTRUCTIONS.md` §4. -/
  | transactional (justification : Name)
  /-- A visibility rule owned by one profile. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

namespace FaultVisibility

/--
`v.RequiresJustification` holds when `v` claims something a profile must prove.

Atomicity across substeps is not observable from the instruction's encoding; it
is a claim about the machine. Marking it here means the §10 profile package can
enumerate exactly which claims are outstanding.
-/
def RequiresJustification : FaultVisibility → Prop
  | .priorEffectsVisible => False
  | .transactional _ | .profileSpecific _ => True

instance : (v : FaultVisibility) → Decidable v.RequiresJustification
  | .priorEffectsVisible => .isFalse (fun h => h)
  | .transactional _ | .profileSpecific _ => .isTrue trivial

end FaultVisibility

/--
An ordered sequence of accesses performed by one operation.

A single-access instruction has a one-element sequence; the sequence is not an
optional elaboration for complex cases, because a uniform representation is what
lets the event and consistency layers treat every operation the same way.
-/
structure SubstepSequence : Type 1 where
  /-- The accesses, in the order the operation performs them. -/
  substeps : List AccessDescriptor
  /-- What survives when one of them fails. No default: see the module comment. -/
  onFault : FaultVisibility

namespace SubstepSequence

/-- A sequence performing exactly one access. -/
def single (d : AccessDescriptor) : SubstepSequence :=
  { substeps := [d], onFault := .priorEffectsVisible }

/-- A sequence that performs no access at all, such as a register-only
instruction. -/
def none_ : SubstepSequence :=
  { substeps := [], onFault := .priorEffectsVisible }

/--
The accesses whose effects remain visible when the substep at `failedAt` fails.

`failedAt` is the index of the substep that did not complete; its own committed
prefix is described by its `AccessStatus` and is not this function's business.
-/
def visibleEffects (seq : SubstepSequence) (failedAt : Nat) : List AccessDescriptor :=
  match seq.onFault with
  | .priorEffectsVisible => seq.substeps.take failedAt
  | .transactional _ => []
  | .profileSpecific _ => seq.substeps.take failedAt

@[simp] theorem visibleEffects_priorEffectsVisible (substeps : List AccessDescriptor)
    (failedAt : Nat) :
    (SubstepSequence.mk substeps .priorEffectsVisible).visibleEffects failedAt =
      substeps.take failedAt := rfl

@[simp] theorem visibleEffects_transactional (substeps : List AccessDescriptor)
    (justification : Name) (failedAt : Nat) :
    (SubstepSequence.mk substeps (.transactional justification)).visibleEffects failedAt =
      [] := rfl

/-- Failure at the first substep exposes nothing, whatever the visibility rule. -/
@[simp] theorem visibleEffects_zero (seq : SubstepSequence) :
    seq.visibleEffects 0 = [] := by
  unfold visibleEffects
  split <;> simp

/-- Nothing outside the sequence is ever made visible by a failure. -/
theorem visibleEffects_sublist (seq : SubstepSequence) (failedAt : Nat) :
    (seq.visibleEffects failedAt).length ≤ seq.substeps.length := by
  unfold visibleEffects
  split <;> simp [List.length_take] <;> omega

/-- `seq.WellFormed` holds when every substep is intrinsically well formed. -/
def WellFormed (seq : SubstepSequence) : Prop :=
  ∀ d ∈ seq.substeps, d.WellFormed

@[simp] theorem wellFormed_none_ : none_.WellFormed := by
  simp [WellFormed, none_]

theorem wellFormed_single {d : AccessDescriptor} (h : d.WellFormed) :
    (single d).WellFormed := by
  simp [WellFormed, single]
  exact h

/--
`seq.ClaimsAtomicity` holds when the sequence asserts more than one access
happens indivisibly.

A profile closing its §10 package must discharge every such claim. A sequence of
length at most one claims nothing, because there is nothing for atomicity to
relate.
-/
def ClaimsAtomicity (seq : SubstepSequence) : Prop :=
  seq.onFault.RequiresJustification ∧ 1 < seq.substeps.length

instance (seq : SubstepSequence) : Decidable seq.ClaimsAtomicity :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem not_claimsAtomicity_single (d : AccessDescriptor) :
    ¬ (single d).ClaimsAtomicity := by
  simp [ClaimsAtomicity, single]

end SubstepSequence

end Grass.Memory
