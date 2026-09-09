import Grass.Platform.Win32.WriteFileCallPlan
import Grass.Platform.Win32.ReturnHomeStackPlan

/-!
# `WriteFile` stack-plan checker

The public stack-plan type stays at the established `WriteFileCallPlan` import
door. Its public loaded-policy producer invokes the common return/home producer
once, then checks the `WriteFile`-specific extension of that exact result.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.ABI Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86
open Grass.Platform.Win32.Loader

namespace Abi

namespace StackPlanFactory

/-- Diagnostics returned by `StackPlanFactory.checked?` and
`StackPlanFactory.deriveLoaded?`. -/
inductive Failure where
  | common (reason : ReturnHome.StackPlanFactory.Failure)
  | fifthRoot
  | homeBufferOverlap
  | homeCountOverlap
  | homeFifthOverlap
  | countReturnOverlap
  | countFifthOverlap
  | returnWritable
  | fifthWritable
deriving Repr

/-- Check only the `WriteFile`-specific extension of an already-derived common
return/home plan.  It never resolves return or home storage itself. -/
def checked? {state : Execution.State} (request : Request) (entry : Entry state request)
    (common : ReturnHome.Plan state) : Except Failure (StackPlan state request) :=
  if fifthRoot : entry.overlappedSlot.provenance.root = common.returnSlot.provenance.root then
  if homeBuffer : common.homeResolved.physical.Disjoint entry.prepared.buffer.physical then
  if homeCount : common.homeResolved.physical.Disjoint entry.prepared.countSlot.physical then
  if homeFifth : common.homeResolved.physical.Disjoint entry.overlappedResolved.physical then
  if countReturn : entry.prepared.countSlot.physical.Disjoint common.returnResolved.physical then
  if countFifth : entry.prepared.countSlot.physical.Disjoint entry.overlappedResolved.physical then
  if returnProtected : ∀ i : Fin 8,
      ¬ (LoanPlan.mk (stackRequests common.returnSlot common.homeSlot entry.overlappedSlot)).WriteAt
        request common.returnSlot.provenance.root (common.returnSlot.range.start + i.val) then
  if fifthProtected : ∀ i : Fin 8,
      ¬ (LoanPlan.mk (stackRequests common.returnSlot common.homeSlot entry.overlappedSlot)).WriteAt
        request entry.overlappedSlot.provenance.root (entry.overlappedSlot.range.start + i.val) then
    .ok
      { toPlan := common
        entry := entry
        fifthRoot := fifthRoot
        homeBufferSeparated := homeBuffer
        homeCountSeparated := homeCount
        homeFifthSeparated := homeFifth
        countReturnSeparated := countReturn
        countFifthSeparated := countFifth
        returnProtected := returnProtected
        overlappedProtected := fifthProtected }
  else .error .fifthWritable
  else .error .returnWritable
  else .error .countFifthOverlap
  else .error .countReturnOverlap
  else .error .homeFifthOverlap
  else .error .homeCountOverlap
  else .error .homeBufferOverlap
  else .error .fifthRoot

/-- Derive the one shared return/home plan from the actual call, then check the
`WriteFile` fifth-slot extension over that exact result. -/
def deriveLoaded? {image : ImageInput} {inputs : EntryInputs} {loaded : LoadedImage image inputs}
    {before : Execution.State} {afterFetch afterRead afterStore : MachineState}
    {displacement : BitVec 32}
    {actualCall : Execution.CallNormal before afterFetch afterRead afterStore displacement}
    (binding : CallEntry.CallPolicy loaded actualCall)
    {request : Request} (entry : Entry actualCall.result request) :
    Except Failure (StackPlan actualCall.result request) :=
  match ReturnHome.StackPlanFactory.deriveLoaded? binding with
  | .error reason => .error (.common reason)
  | .ok common => checked? request entry common

/-- A successful extension retains both exact inputs used to build it. -/
theorem checked?_fields {state : Execution.State} {request : Request}
    {entry : Entry state request} {common : ReturnHome.Plan state}
    {result : StackPlan state request}
    (success : checked? request entry common = .ok result) :
    result.toPlan = common ∧ result.entry = entry := by
  unfold checked? at success
  repeat' split at success <;> try contradiction
  cases success
  exact ⟨rfl, rfl⟩

/-- A successful extension retains the exact caller-supplied common plan. -/
theorem checked?_plan {state : Execution.State} {request : Request}
    {entry : Entry state request} {common : ReturnHome.Plan state}
    {result : StackPlan state request}
    (success : checked? request entry common = .ok result) : result.toPlan = common :=
  (checked?_fields success).1

/-- A successful extension retains the exact caller-supplied `WriteFile` entry
evidence, including its prepared arguments and fifth-slot resolution. -/
theorem checked?_entry {state : Execution.State} {request : Request}
    {entry : Entry state request} {common : ReturnHome.Plan state}
    {result : StackPlan state request}
    (success : checked? request entry common = .ok result) : result.entry = entry :=
  (checked?_fields success).2

/-- A public successful result carries the exact common plan produced by the
shared loaded-policy door and the exact supplied `WriteFile` entry. -/
theorem loaded_common {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {actualCall : Execution.CallNormal before afterFetch afterRead afterStore displacement}
    {binding : CallEntry.CallPolicy loaded actualCall} {request : Request}
    {entry : Entry actualCall.result request} {plan : StackPlan actualCall.result request}
    (success : deriveLoaded? binding entry = .ok plan) :
    ∃ common, ReturnHome.StackPlanFactory.deriveLoaded? binding = .ok common ∧
      plan.toPlan = common ∧ plan.entry = entry := by
  unfold deriveLoaded? at success
  split at success
  · contradiction
  · rename_i common commonSuccess
    exact ⟨common, commonSuccess, (checked?_fields success).1, (checked?_fields success).2⟩

/-- The public `WriteFile` producer retains the continuation extracted by the
single shared return/home producer. -/
theorem loaded_continuation_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {actualCall : Execution.CallNormal before afterFetch afterRead afterStore displacement}
    {binding : CallEntry.CallPolicy loaded actualCall} {request : Request}
    {entry : Entry actualCall.result request} {plan : StackPlan actualCall.result request}
    (success : deriveLoaded? binding entry = .ok plan) :
    plan.continuation = actualCall.fetch.site.fallthroughRip := by
  obtain ⟨common, commonSuccess, retained, _⟩ := loaded_common success
  change plan.toPlan.continuation = actualCall.fetch.site.fallthroughRip
  rw [retained]
  exact ReturnHome.StackPlanFactory.loaded_continuation_exact commonSuccess

/-- The public producer retains the actual CALL store provenance selected by
the shared return/home producer. -/
theorem loaded_return_provenance_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {actualCall : Execution.CallNormal before afterFetch afterRead afterStore displacement}
    {binding : CallEntry.CallPolicy loaded actualCall} {request : Request}
    {entry : Entry actualCall.result request} {plan : StackPlan actualCall.result request}
    (success : deriveLoaded? binding entry = .ok plan) :
    plan.returnSlot.provenance = actualCall.storeDescriptor.provenance := by
  obtain ⟨common, commonSuccess, retained, _⟩ := loaded_common success
  change plan.toPlan.returnSlot.provenance = actualCall.storeDescriptor.provenance
  rw [retained]
  exact (ReturnHome.StackPlanFactory.exact_fields commonSuccess).2.1

/-- The public producer retains the actual CALL store range selected by the
shared return/home producer. -/
theorem loaded_return_range_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {actualCall : Execution.CallNormal before afterFetch afterRead afterStore displacement}
    {binding : CallEntry.CallPolicy loaded actualCall} {request : Request}
    {entry : Entry actualCall.result request} {plan : StackPlan actualCall.result request}
    (success : deriveLoaded? binding entry = .ok plan) :
    plan.returnSlot.range = actualCall.storeDescriptor.range := by
  obtain ⟨common, commonSuccess, retained, _⟩ := loaded_common success
  change plan.toPlan.returnSlot.range = actualCall.storeDescriptor.range
  rw [retained]
  exact (ReturnHome.StackPlanFactory.exact_fields commonSuccess).2.2

/-- The public producer retains exactly the supplied `WriteFile` entry evidence. -/
theorem loaded_entry_exact {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {before : Execution.State}
    {afterFetch afterRead afterStore : MachineState} {displacement : BitVec 32}
    {actualCall : Execution.CallNormal before afterFetch afterRead afterStore displacement}
    {binding : CallEntry.CallPolicy loaded actualCall} {request : Request}
    {entry : Entry actualCall.result request} {plan : StackPlan actualCall.result request}
    (success : deriveLoaded? binding entry = .ok plan) : plan.entry = entry := by
  obtain ⟨_, _, _, retained⟩ := loaded_common success
  exact retained

end StackPlanFactory
end Abi
end Grass.Platform.Win32.WriteFile
