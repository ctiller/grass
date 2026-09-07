import Grass.Construct.Fragment.Verified

/-!
# Exact generic scratch selection

`ScratchRequest` records an ordered candidate set and the exact register set the
caller reports live. `checkScratch` selects the first non-live candidate and
returns evidence of both membership and non-liveness. It does not derive machine
liveness; connecting the request to an instruction effect model belongs to the
machine backend.

`withSelectedScratch` is the checked term-level binder. Its body may compute
source from the selected register, but must return one fixed `BlockContract`, so
the register identity cannot appear in the result contract. The binder emits no
instructions of its own.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- Ordered scratch candidates and the exact caller-supplied live set. -/
structure ScratchRequest (Register : Type u) where
  candidates : List Register
  live : List Register
deriving Repr

namespace ScratchRequest

variable {Register : Type u} [DecidableEq Register]

/-- First candidate, in authored order, that is absent from the live set. -/
def available? (request : ScratchRequest Register) : Option Register :=
  request.candidates.find? fun register => decide (register ∉ request.live)

/-- Structural validity requires candidate identities to be unique. -/
def WellFormed (request : ScratchRequest Register) : Prop :=
  request.candidates.Nodup

instance (request : ScratchRequest Register) : Decidable request.WellFormed :=
  inferInstanceAs (Decidable request.candidates.Nodup)

end ScratchRequest

/-- One exact selected scratch register with executable selection evidence. -/
structure CheckedScratch {Register : Type u} [DecidableEq Register]
    (request : ScratchRequest Register) where
  register : Register
  requestValid : request.WellFormed
  selectedExact : request.available? = some register

namespace CheckedScratch

variable {Register : Type u} [DecidableEq Register]
  {request : ScratchRequest Register}

/-- The selected register belongs to the request's authored candidate set. -/
theorem candidateMember (checked : CheckedScratch request) :
    checked.register ∈ request.candidates :=
  List.mem_of_find?_eq_some checked.selectedExact

/-- The selected register is absent from the exact caller-supplied live set. -/
theorem notLive (checked : CheckedScratch request) :
    checked.register ∉ request.live := by
  have accepted : decide (checked.register ∉ request.live) = true :=
    List.find?_some (p := fun register : Register =>
      decide (register ∉ request.live)) checked.selectedExact
  exact of_decide_eq_true accepted

end CheckedScratch

/-- Structured scratch-selection rejection. -/
inductive ScratchError (Register : Type u) where
  | duplicateCandidates (candidates : List Register)
  | noAvailable
deriving Repr, DecidableEq

/-- Check candidate uniqueness and select the first non-live register exactly. -/
def checkScratch {Register : Type u} [DecidableEq Register]
    (request : ScratchRequest Register) :
    Except (ScratchError Register) (CheckedScratch request) :=
  if unique : request.WellFormed then
    match found : request.available? with
    | none => .error .noAvailable
    | some register => .ok ⟨register, unique, found⟩
  else
    .error (.duplicateCandidates request.candidates)

/-- Exact selected register exposed only to a scratch-bound body. -/
structure ScratchHandle {Register : Type u} [DecidableEq Register]
    {request : ScratchRequest Register} (checked : CheckedScratch request) where
  register : Register
  registerExact : register = checked.register

namespace CheckedScratch

/-- Canonical handle for the exact selected register. -/
def handle {Register : Type u} [DecidableEq Register]
    {request : ScratchRequest Register} (checked : CheckedScratch request) :
    ScratchHandle checked :=
  ⟨checked.register, rfl⟩

end CheckedScratch

/--
Run a verified fixed-contract body with the exact checked scratch selection.

`withSelectedScratch` is definitionally the body at `CheckedScratch.handle`, so
it contributes no hidden source or proof. The request's correspondence to real
machine liveness remains an explicit backend obligation.
-/
def withSelectedScratch {Register : Type u} [DecidableEq Register]
    {Instruction : Type v} {State : Type w} {Effect : Type x}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {contract : BlockContract State} {request : ScratchRequest Register}
    (checked : CheckedScratch request)
    (body : ScratchHandle checked →
      VerifiedFragment semantics effectModel contract) :
    VerifiedFragment semantics effectModel contract :=
  body checked.handle

/-- `withSelectedScratch_source` exposes the exact body source unchanged. -/
@[simp] theorem withSelectedScratch_source
    {Register : Type u} [DecidableEq Register]
    {Instruction : Type v} {State : Type w} {Effect : Type x}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {contract : BlockContract State} {request : ScratchRequest Register}
    (checked : CheckedScratch request)
    (body : ScratchHandle checked →
      VerifiedFragment semantics effectModel contract) :
    (withSelectedScratch checked body).source = (body checked.handle).source :=
  rfl

end Grass.Construct
