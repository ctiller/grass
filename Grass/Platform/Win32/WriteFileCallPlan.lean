import Grass.Platform.Win32.WriteFileAbi
import Grass.Grammar.Endian

/-!
# Bounded `WriteFile` call custody and entry-stack observations

This module describes the finite authority that a `WriteFile` call will need
and records already-resolved facts about its callee-entry stack.  It neither
performs a `CALL` nor mints or hands off any authority.
-/

namespace Grass.Platform.Win32.WriteFile

open Grass.ABI Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.ISA.X86

/-- The explicit authority extension for one `WriteFile` request.  The
semantic buffer and count-slot permissions are fixed by `Request.loans`; this
list is only for additional, concrete call custody. -/
structure LoanPlan where
  additional : List CallProtocol.LoanRequest

/-- The complete request list, with the semantic requests always first. -/
def LoanPlan.requests (plan : LoanPlan) (request : Request) : List CallProtocol.LoanRequest :=
  request.loans ++ plan.additional

/-- A read footprint is either the fixed input buffer or an explicitly added
read-authorized loan containing the observed range. -/
def LoanPlan.ReadFootprint (plan : LoanPlan) (request : Request)
    (provenance : Provenance) (range : ByteRange) : Prop :=
  (provenance = request.buffer.provenance ∧ request.buffer.range.Contains range) ∨
  ∃ loan ∈ plan.additional,
    loan.provenance = provenance ∧ loan.rights.read = true ∧ loan.range.Contains range

/-- A write footprint is either the fixed count slot or an explicitly added
write-authorized loan containing the observed range. -/
def LoanPlan.WriteFootprint (plan : LoanPlan) (request : Request)
    (provenance : Provenance) (range : ByteRange) : Prop :=
  (provenance = request.countSlot.provenance ∧ request.countSlot.range.Contains range) ∨
  ∃ loan ∈ plan.additional,
    loan.provenance = provenance ∧ loan.rights.write = true ∧ loan.range.Contains range

/-- The pointwise write boundary used to frame a provider memory transition. -/
def LoanPlan.WriteAt (plan : LoanPlan) (request : Request) (root : AllocId)
    (offset : Nat) : Prop :=
  (root = request.countSlot.provenance.root ∧ request.countSlot.range.Covers offset) ∨
  ∃ loan ∈ plan.additional,
    loan.provenance.root = root ∧ loan.rights.write = true ∧ loan.range.Covers offset

namespace Abi

/-- Resolved, initialized bytes occupying a callee-entry return-address slot. -/
structure InitializedReturnQword {memory : MemoryState} {slot : Argument}
    (resolved : Resolved memory slot) (continuation : BitVec 64) where
  bytes : Grass.Grammar.SizedByteArray 8
  initialized : ∀ i : Fin 8,
    resolved.toResolvedAccess.cellAt? (slot.range.start + i.val) =
      some (bytes.1[i.val], true)
  continuationMatches : Grass.Grammar.littleEndianToBitVec bytes = continuation

/-- The fixed ABI loans for the return-address, writable home, and nullable
fifth-argument stack slots, in callee-entry order. -/
def stackRequests (returnSlot homeSlot overlappedSlot : Argument) :
    List CallProtocol.LoanRequest :=
  [⟨.loan, returnSlot.provenance, returnSlot.range, .readOnly⟩,
   ⟨.loan, homeSlot.provenance, homeSlot.range, .readWrite⟩,
   ⟨.loan, overlappedSlot.provenance, overlappedSlot.range, .readOnly⟩]

/-- Concrete Win64 callee-entry stack observations for `WriteFile`.

The fields describe memory which has already been resolved against `state`; they
do not state that a call instruction ran, that a continuation was fetched, or
that the loans below have been issued. -/
structure StackPlan (state : Execution.State) (request : Request) where
  entry : Entry state request
  continuation : BitVec 64
  returnSlot : Argument
  returnResolved : Resolved state.machine.memory returnSlot
  returnCPU : returnSlot.provenance.space = .cpuVirtual
  returnStack : returnResolved.allocation.source = .stack
  returnSize : returnSlot.range.size = returnAddressBytes
  returnAddress :
    (addressOf returnResolved.base returnSlot.range.start).toNat = (state.gpr .rsp).toNat
  returnObserved : InitializedReturnQword returnResolved continuation
  homeSlot : Argument
  homeResolved : Resolved state.machine.memory homeSlot
  homeCPU : homeSlot.provenance.space = .cpuVirtual
  homeRoot : homeSlot.provenance.root = returnSlot.provenance.root
  homeSize : homeSlot.range.size = homeSpaceBytes
  homeAddress :
    (addressOf homeResolved.base homeSlot.range.start).toNat =
      (state.gpr .rsp).toNat + returnAddressBytes
  fifthRoot : entry.overlappedSlot.provenance.root = returnSlot.provenance.root
  homeBufferSeparated : homeResolved.physical.Disjoint entry.prepared.buffer.physical
  homeCountSeparated : homeResolved.physical.Disjoint entry.prepared.countSlot.physical
  homeReturnSeparated : homeResolved.physical.Disjoint returnResolved.physical
  homeFifthSeparated : homeResolved.physical.Disjoint entry.overlappedResolved.physical
  countReturnSeparated : entry.prepared.countSlot.physical.Disjoint returnResolved.physical
  countFifthSeparated : entry.prepared.countSlot.physical.Disjoint
    entry.overlappedResolved.physical
  returnProtected : ∀ i : Fin 8,
    ¬ (LoanPlan.mk (stackRequests returnSlot homeSlot entry.overlappedSlot)).WriteAt request
      returnSlot.provenance.root (returnSlot.range.start + i.val)
  overlappedProtected : ∀ i : Fin 8,
    ¬ (LoanPlan.mk (stackRequests returnSlot homeSlot entry.overlappedSlot)).WriteAt request
      entry.overlappedSlot.provenance.root (entry.overlappedSlot.range.start + i.val)

/-- The ABI-specific loans in the exact callee-entry stack order. -/
def StackPlan.requests {state : Execution.State} {request : Request}
    (plan : StackPlan state request) : List CallProtocol.LoanRequest :=
  stackRequests plan.returnSlot plan.homeSlot plan.entry.overlappedSlot

/-- The full custody plan for this ABI binding: semantic permissions followed by
the fixed-order return, home, and fifth-argument stack permissions. -/
def StackPlan.loanPlan {state : Execution.State} {request : Request}
    (plan : StackPlan state request) : LoanPlan :=
  { additional := plan.requests }

end Abi
end Grass.Platform.Win32.WriteFile
