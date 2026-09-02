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

*Across* steps, a `SubstepSequence` says what survives when a later step fails.
`rep movsb` is not one access with a byte count; it is a sequence whose earlier
iterations completed and stay completed.

## Not every step is an access

`div [mem]` reads its divisor and then raises `#DE` from the division itself. The
faulting step performs no memory access, and yet the read before it has already
happened — exactly what §1 requires a profile to be able to state.

A sequence of accesses alone cannot state it: there is no index to name the
faulting step. `Substep` therefore has a `compute` case for a step that can fault
without touching memory. `div [mem]` is `[access divisorRead, compute [#DE]]`,
and failure at index 1 leaves the read visible.

## `onFault` has no default value

`docs/INSTRUCTIONS.md` §4 says a macro "is not semantically atomic unless a target
theorem proves that property", and the same holds for an instruction. An author
who omits the declaration gets a missing-field error, not an assumption of
atomicity. `transactional` additionally carries the name of the justification that
establishes it, so claiming atomicity leaves a citation trail.

## An unknown rule yields no answer

`visibleEffects?` returns `Option`, and `profileSpecific` yields `none`. This
module does not know what a profile-owned visibility rule says, and
`docs/FOUNDATION.md` law 8 requires it to reject rather than approximate. An
earlier version returned the `priorEffectsVisible` answer for `profileSpecific`,
which is a plausible guess and therefore the worst possible behavior: it would
have silently produced the wrong survivor set for exactly the cases a profile
introduced its own rule to describe. Intel does not guarantee that a store split
across a page boundary is all-or-nothing to other agents, so this is a case that
occurs in the first profile, not a hypothetical one.
-/

namespace Grass.Memory

open Grass.Core

/--
What remains visible when a step of a sequence fails.

There is deliberately no "unspecified" case. The effect of a failure partway
through a multi-step instruction is exactly the kind of thing a permissive
default would get wrong in the safe-looking direction.
-/
inductive FaultVisibility where
  /-- Steps that completed before the failure remain visible. This is the default
  *behavior* of most hardware, though not a default *value* here. -/
  | priorEffectsVisible
  /-- No step is visible unless all are. Requires a target theorem, named by
  `justification`, per `docs/INSTRUCTIONS.md` §4. -/
  | transactional (justification : Name)
  /-- A visibility rule owned by one profile. This module cannot answer questions
  about it, and `visibleEffects?` says so rather than guessing. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

namespace FaultVisibility

/--
`v.RequiresJustification` holds when `v` claims something a profile must prove.

Atomicity across steps is not observable from an instruction's encoding; it is a
claim about the machine. Marking it here means the §10 profile package can
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
One step of an operation.

`compute` covers a step that can fault without accessing memory. It carries the
faults it may raise, because a compute step that cannot fail does nothing
observable and has no reason to be in the sequence.
-/
inductive Substep where
  /-- The step performs this memory access. -/
  | access (descriptor : AccessDescriptor)
  /-- The step touches no memory but may raise one of these faults. -/
  | compute (faults : List FaultClassId)
deriving DecidableEq, Repr

namespace Substep

/-- The access this step performs, if it performs one. -/
def descriptor? : Substep → Option AccessDescriptor
  | .access d => some d
  | .compute _ => Option.none

/-- The faults this step may raise. -/
def faults : Substep → List FaultClassId
  | .access d => d.admittedFaults
  | .compute faults => faults

/--
`step.WellFormedIn table` holds when an access step names a space the table
declares and is well formed in it, and a compute step has a reason to exist.

Table-relative because `AccessDescriptor.WellFormedIn` is: a descriptor names its
space and the profile decides what that space is.
-/
def WellFormedIn (table : AddressSpaceTable) : Substep → Prop
  | .access d =>
      match table.find? d.space with
      | some space => d.WellFormedIn space
      | Option.none => False
  | .compute faults => faults ≠ []

instance (table : AddressSpaceTable) (step : Substep) :
    Decidable (step.WellFormedIn table) := by
  cases step with
  | access d =>
    show Decidable (match table.find? d.space with
      | some space => d.WellFormedIn space
      | Option.none => False)
    cases table.find? d.space <;> simp <;> infer_instance
  | compute faults => exact inferInstanceAs (Decidable (faults ≠ []))

@[simp] theorem descriptor?_access (d : AccessDescriptor) :
    (Substep.access d).descriptor? = some d := rfl

@[simp] theorem descriptor?_compute (faults : List FaultClassId) :
    (Substep.compute faults).descriptor? = Option.none := rfl

/-- A compute step that cannot fault is not a step. -/
theorem not_wellFormedIn_compute_nil (table : AddressSpaceTable) :
    ¬ (Substep.compute []).WellFormedIn table := fun h => h rfl

/-- A step naming a space the profile never declared is not well formed, whatever
else is true of it. -/
theorem not_wellFormedIn_of_undeclared {table : AddressSpaceTable} {d : AccessDescriptor}
    (h : ¬ table.Declares d.space) : ¬ (Substep.access d).WellFormedIn table := by
  show ¬ (match table.find? d.space with
    | some space => d.WellFormedIn space
    | Option.none => False)
  cases hfind : table.find? d.space with
  | none => simp
  | some space => exact absurd (by simp [AddressSpaceTable.Declares, hfind]) h

end Substep

/--
An ordered sequence of steps performed by one operation.

A single-access instruction has a one-element sequence; the sequence is not an
optional elaboration for complex cases, because a uniform representation is what
lets the event and consistency layers treat every operation the same way.
-/
structure SubstepSequence where
  /-- The steps, in the order the operation performs them. -/
  substeps : List Substep
  /-- What survives when one of them fails. No default: see the module comment. -/
  onFault : FaultVisibility
deriving DecidableEq, Repr

namespace SubstepSequence

/-- A sequence performing exactly one access. -/
def single (d : AccessDescriptor) : SubstepSequence :=
  { substeps := [.access d], onFault := .priorEffectsVisible }

/-- A sequence that performs no access and cannot fault, such as a register-only
instruction. -/
def none_ : SubstepSequence :=
  { substeps := [], onFault := .priorEffectsVisible }

/-- The accesses this sequence performs, in order. -/
def accesses (seq : SubstepSequence) : List AccessDescriptor :=
  seq.substeps.filterMap Substep.descriptor?

/--
The accesses whose effects remain visible when the step at `failedAt` fails, or
`none` when the visibility rule belongs to a profile this module cannot consult.

`failedAt` is the index of the step that did not complete; its own committed
prefix, if it was an access, is described by its `AccessStatus` and is not this
function's business.
-/
def visibleEffects? (seq : SubstepSequence) (failedAt : Nat) :
    Option (List AccessDescriptor) :=
  match seq.onFault with
  | .priorEffectsVisible =>
      some ((seq.substeps.take failedAt).filterMap Substep.descriptor?)
  | .transactional _ => some []
  | .profileSpecific _ => Option.none

/--
Whether the faulting substep's *own* committed prefix survives.

`visibleEffects?` answers for the substeps before the failure. This answers for
the failing one, and they are different questions: a store that faults partway
through has written the bytes it wrote, which `priorEffectsVisible` admits and
`transactional` does not.

Not having asked the second question was a defect. `runStep` took
`visibleEffects?`'s answer for the prefix and then committed the faulting
substep unconditionally, so a `transactional` sequence discarded every completed
substep and kept the faulting one's partial write — the exact reverse of "no step
is visible unless all are". Local adversarial review built that case.

`profileSpecific` answers `false` because this module cannot answer for it;
`visibleEffects?` returns `none` there and `step` rejects, so the value is the
conservative one for a branch that is not reached rather than a guess that is.
-/
def faultingEffectVisible (seq : SubstepSequence) : Bool :=
  match seq.onFault with
  | .priorEffectsVisible => true
  | .transactional _ => false
  | .profileSpecific _ => false

@[simp] theorem faultingEffectVisible_priorEffectsVisible (substeps : List Substep) :
    (SubstepSequence.mk substeps .priorEffectsVisible).faultingEffectVisible = true := rfl

/-- **A transactional sequence exposes nothing when it faults**, its own faulting
substep included. With `visibleEffects?_transactional`, this is the pair that makes
`FaultVisibility.transactional`'s "no step is visible unless all are" true of the
transition rather than only of the prefix. -/
@[simp] theorem faultingEffectVisible_transactional (substeps : List Substep)
    (justification : Name) :
    (SubstepSequence.mk substeps (.transactional justification)).faultingEffectVisible =
      false := rfl

@[simp] theorem visibleEffects?_priorEffectsVisible (substeps : List Substep)
    (failedAt : Nat) :
    (SubstepSequence.mk substeps .priorEffectsVisible).visibleEffects? failedAt =
      some ((substeps.take failedAt).filterMap Substep.descriptor?) := rfl

@[simp] theorem visibleEffects?_transactional (substeps : List Substep)
    (justification : Name) (failedAt : Nat) :
    (SubstepSequence.mk substeps (.transactional justification)).visibleEffects?
      failedAt = some [] := rfl

/-- A profile-owned rule yields no answer here. -/
@[simp] theorem visibleEffects?_profileSpecific (substeps : List Substep)
    (name : Name) (failedAt : Nat) :
    (SubstepSequence.mk substeps (.profileSpecific name)).visibleEffects? failedAt =
      Option.none := rfl

/-- Failure at the first step exposes nothing, whatever the visibility rule
answers. -/
theorem visibleEffects?_zero (seq : SubstepSequence) :
    ∀ visible, seq.visibleEffects? 0 = some visible → visible = [] := by
  intro visible h
  unfold visibleEffects? at h
  split at h <;> simp_all

/--
Nothing outside the sequence is ever made visible by a failure.

Stated as containment rather than as a length bound. An earlier version proved
only `length ≤ length`, which is not the claim its own docstring made: a length
bound says nothing about *which* accesses appear.
-/
theorem mem_substeps_of_mem_visibleEffects? {seq : SubstepSequence} {failedAt : Nat}
    {visible : List AccessDescriptor} (h : seq.visibleEffects? failedAt = some visible)
    {d : AccessDescriptor} (hd : d ∈ visible) : Substep.access d ∈ seq.substeps := by
  unfold visibleEffects? at h
  split at h
  · cases h
    obtain ⟨step, hstep, hsome⟩ := List.mem_filterMap.mp hd
    have : step = Substep.access d := by
      cases step with
      | access d' => simpa using hsome
      | compute _ => simp at hsome
    exact this ▸ List.mem_of_mem_take hstep
  · cases h; simp at hd
  · exact absurd h (by simp)

/-- `seq.WellFormedIn table` holds when every step is well formed in `table`. -/
def WellFormedIn (seq : SubstepSequence) (table : AddressSpaceTable) : Prop :=
  ∀ step ∈ seq.substeps, step.WellFormedIn table

@[simp] theorem wellFormedIn_none_ (table : AddressSpaceTable) :
    none_.WellFormedIn table := by
  simp [WellFormedIn, none_]

theorem wellFormedIn_single {table : AddressSpaceTable} {d : AccessDescriptor}
    {space : AddressSpace} (hfind : table.find? d.space = some space)
    (h : d.WellFormedIn space) : (single d).WellFormedIn table := by
  simp only [WellFormedIn, single, List.mem_singleton]
  rintro step rfl
  show (match table.find? d.space with
    | some space => d.WellFormedIn space
    | Option.none => False)
  rw [hfind]
  exact h

instance (seq : SubstepSequence) (table : AddressSpaceTable) :
    Decidable (seq.WellFormedIn table) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/--
`seq.ClaimsAtomicity` holds when the sequence asserts more than one step happens
indivisibly.

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
