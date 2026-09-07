import Grass.Construct.Fragment.Verified
import Grass.Construct.StackObjectSource

/-!
# Proof-bearing checked stack-object backend seam

`StackObjectVerifiedBackend` requires the machine owner to provide every
verified load/store fragment and equality to the corresponding transparent
checked-slice source. `StackObjectVerifiedBackend.load` and
`StackObjectVerifiedBackend.store` only project those supplied witnesses.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Layout Grass.Construct.Fragment

universe u v w x

/-- Machine-supplied verified implementations of checked stack-slice operations. -/
structure StackObjectVerifiedBackend (Instruction : Type u) (Operand : Type v)
    (State : Type w) (Effect : Type x) (semantics : Semantics Instruction State)
    (effectModel : EffectModel Instruction Effect) where
  source : StackObjectSourceBackend Instruction Operand
  loadContract : {profile : LayoutProfile} →
    {checked : CheckedStackLayout profile} → {slot : StackObjectRef checked} →
    CheckedStackSlice slot → Operand → BlockContract State
  storeContract : {profile : LayoutProfile} →
    {checked : CheckedStackLayout profile} → {slot : StackObjectRef checked} →
    CheckedStackSlice slot → Operand → BlockContract State
  loadVerified : {profile : LayoutProfile} →
    {checked : CheckedStackLayout profile} → {slot : StackObjectRef checked} →
    (slice : CheckedStackSlice slot) → (destination : Operand) →
    VerifiedFragment semantics effectModel (loadContract slice destination)
  storeVerified : {profile : LayoutProfile} →
    {checked : CheckedStackLayout profile} → {slot : StackObjectRef checked} →
    (slice : CheckedStackSlice slot) → (sourceOperand : Operand) →
    VerifiedFragment semantics effectModel (storeContract slice sourceOperand)
  loadSourceExact : ∀ {profile checked slot}
    (slice : @CheckedStackSlice profile checked slot) (destination : Operand),
    (loadVerified slice destination).source = source.load slice destination
  storeSourceExact : ∀ {profile checked slot}
    (slice : @CheckedStackSlice profile checked slot) (sourceOperand : Operand),
    (storeVerified slice sourceOperand).source = source.store slice sourceOperand

namespace StackObjectVerifiedBackend

variable {Instruction : Type u} {Operand : Type v} {State : Type w} {Effect : Type x}
  {semantics : Semantics Instruction State}
  {effectModel : EffectModel Instruction Effect}
  {profile : LayoutProfile} {checked : CheckedStackLayout profile}
  {slot : StackObjectRef checked}

/-- Transparent verified load projection for one checked slice. -/
def load
    (backend : StackObjectVerifiedBackend Instruction Operand State Effect
      semantics effectModel)
    (slice : CheckedStackSlice slot) (destination : Operand) :=
  backend.loadVerified slice destination

/-- Transparent verified store projection for one checked slice. -/
def store
    (backend : StackObjectVerifiedBackend Instruction Operand State Effect
      semantics effectModel)
    (slice : CheckedStackSlice slot) (sourceOperand : Operand) :=
  backend.storeVerified slice sourceOperand

/-- Transparent verified nominal load projection. -/
def loadNamed
    (backend : StackObjectVerifiedBackend Instruction Operand State Effect
      semantics effectModel)
    {name : Grass.Core.Name} (slice : NamedCheckedStackSlice checked name)
    (destination : Operand) :=
  backend.load slice.checkedSlice destination

/-- Transparent verified nominal store projection. -/
def storeNamed
    (backend : StackObjectVerifiedBackend Instruction Operand State Effect
      semantics effectModel)
    {name : Grass.Core.Name} (slice : NamedCheckedStackSlice checked name)
    (sourceOperand : Operand) :=
  backend.store slice.checkedSlice sourceOperand

end StackObjectVerifiedBackend

end Grass.Construct
