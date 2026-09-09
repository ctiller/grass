import Grass.Platform.Win32.CallMemory
import Grass.ABI.Win64.Convention
import Grass.ISA.X86.Execution.State
import Grass.Grammar.Endian

/-! Shared Win64 return-address and home-space plan for returning API calls. -/

namespace Grass.Platform.Win32.ReturnHome

open Grass.ABI Grass.Core Grass.Memory Grass.ISA.X86

/-- Width of a 64-bit near-call return address. -/
def returnAddressBytes : Nat := Grass.ISA.X86.Width.bits .w64 / 8

/-- Win64 caller-provided register home area. -/
abbrev homeSpaceBytes : Nat := Win64.shadowSpaceBytes

def stackRequests (returnSlot homeSlot : CallMemory.Argument) :
    List Grass.Op.CallProtocol.LoanRequest :=
  [⟨.loan, returnSlot.provenance, returnSlot.range, .readOnly⟩,
   ⟨.loan, homeSlot.provenance, homeSlot.range, .readWrite⟩]

/-- Resolved initialized bytes in the return-address slot. -/
structure InitializedReturnQword {memory : MemoryState} {slot : CallMemory.Argument}
    (resolved : CallMemory.Resolved memory slot) (continuation : BitVec 64) where
  bytes : Grass.Grammar.SizedByteArray 8
  initialized : ∀ i : Fin 8,
    resolved.toResolvedAccess.cellAt? (slot.range.start + i.val) =
      some (bytes.1[i.val], true)
  continuationMatches : Grass.Grammar.littleEndianToBitVec bytes = continuation

/-- The common resolved return-address and caller home-space prefix. -/
structure Plan (state : Execution.State) where
  continuation : BitVec 64
  returnSlot : CallMemory.Argument
  returnResolved : CallMemory.Resolved state.machine.memory returnSlot
  returnCPU : returnSlot.provenance.space = .cpuVirtual
  returnStack : returnResolved.allocation.source = .stack
  returnSize : returnSlot.range.size = returnAddressBytes
  returnAddress :
    (addressOf returnResolved.base returnSlot.range.start).toNat = (state.gpr .rsp).toNat
  returnObserved : InitializedReturnQword returnResolved continuation
  homeSlot : CallMemory.Argument
  homeResolved : CallMemory.Resolved state.machine.memory homeSlot
  homeCPU : homeSlot.provenance.space = .cpuVirtual
  homeRoot : homeSlot.provenance.root = returnSlot.provenance.root
  homeSize : homeSlot.range.size = homeSpaceBytes
  homeAddress :
    (addressOf homeResolved.base homeSlot.range.start).toNat =
      (state.gpr .rsp).toNat + returnAddressBytes
  homeReturnSeparated : homeResolved.physical.Disjoint returnResolved.physical

end Grass.Platform.Win32.ReturnHome
