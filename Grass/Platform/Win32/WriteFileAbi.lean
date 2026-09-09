import Grass.ABI.Win64.Convention
import Grass.ISA.X86.Execution.State
import Grass.Platform.Win32.WriteFileArguments

/-!
# WriteFile x64 entry argument correspondence

This module relates an actual x86 architectural state to a prepared `WriteFile`
request. It does not perform a `CALL`, read the source buffer, or claim that the
provider returns.

Microsoft's x64 calling convention assigns the first four integer arguments to
RCX, RDX, R8, and R9 and places later arguments on the stack after the return
address and caller-provided home area:
https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention

Microsoft documents `WriteFile`'s five parameters, including the nullable fifth
`LPOVERLAPPED` parameter and the DWORD byte count:
https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile
-/

namespace Grass.Platform.Win32.WriteFile.Abi

open Grass.ABI Grass.Core Grass.ISA.X86 Grass.Memory
open Grass.Platform.Win32.WriteFile

/-- Bytes occupied by the near `CALL` return address in 64-bit mode. This is
derived from the x86 architectural 64-bit operand width; the numerically equal
Win64 entry-alignment residue is a separate convention fact. -/
def returnAddressBytes : Nat := Grass.ISA.X86.Width.bits .w64 / 8

/-- The Win64 caller-provided register home area. -/
abbrev homeSpaceBytes : Nat := Win64.shadowSpaceBytes

/-- Offset of `WriteFile`'s fifth argument from callee-entry RSP. -/
def overlappedSlotOffset : Nat := returnAddressBytes + homeSpaceBytes

/-- An exact initialized null pointer in a resolved eight-byte stack slot. -/
def InitializedNullQword {memory : MemoryState} {slot : Argument}
    (resolved : Resolved memory slot) : Prop :=
  slot.range.size = 8 ∧ ∀ i : Fin 8,
    resolved.toResolvedAccess.cellAt? (slot.range.start + i.val) = some (0, true)

instance {memory : MemoryState} {slot : Argument} (resolved : Resolved memory slot) :
    Decidable (InitializedNullQword resolved) := by
  unfold InitializedNullQword
  infer_instance

/-- Fixed Win64 `WriteFile` entry binding consumed by the x86 call wrapper.
The three pointer-bearing arguments retain their independently resolved memory
evidence; numeric equality alone never manufactures provenance. -/
structure Entry (state : Execution.State) (request : Request) where
  prepared : Prepared state.machine.memory request
  overlappedSlot : Argument
  overlappedResolved : Resolved state.machine.memory overlappedSlot
  overlappedCPU : overlappedSlot.provenance.space = .cpuVirtual
  handle : state.gpr .rcx = request.handle
  bufferAddress : state.gpr .rdx =
    addressOf prepared.buffer.base request.buffer.range.start
  requestedLow : BitVec.setWidth 32 (state.gpr .r8) = request.requested
  countAddress : state.gpr .r9 =
    addressOf prepared.countSlot.base request.countSlot.range.start
  overlappedAddress :
    (addressOf overlappedResolved.base overlappedSlot.range.start).toNat =
      (state.gpr .rsp).toNat + overlappedSlotOffset
  overlappedNull : InitializedNullQword overlappedResolved

theorem Entry.requested_low {state : Execution.State} {request : Request}
    (entry : Entry state request) :
    BitVec.setWidth 32 (state.gpr .r8) = request.requested := entry.requestedLow

theorem Entry.buffer_size {state : Execution.State} {request : Request}
    (entry : Entry state request) :
    request.buffer.range.size = request.requested.toNat := entry.prepared.bufferSize

theorem Entry.bytes_size {state : Execution.State} {request : Request}
    (entry : Entry state request) :
    request.bytes.length = request.requested.toNat := entry.prepared.bytesSize

theorem Entry.count_size {state : Execution.State} {request : Request}
    (entry : Entry state request) : request.countSlot.range.size = 4 :=
  entry.prepared.countSize

theorem Entry.input_matches {state : Execution.State} {request : Request}
    (entry : Entry state request) : InputMatches state.machine.memory request :=
  entry.prepared.input

theorem Entry.overlapped_slot_size {state : Execution.State} {request : Request}
    (entry : Entry state request) : entry.overlappedSlot.range.size = 8 :=
  entry.overlappedNull.1

/-- The exact natural-number stack address equality rules out wrapping RSP past
the 64-bit address space when locating the fifth argument. -/
theorem Entry.overlapped_address_no_wrap {state : Execution.State} {request : Request}
    (entry : Entry state request) :
    (state.gpr .rsp).toNat + overlappedSlotOffset < 2 ^ 64 := by
  rw [← entry.overlappedAddress]
  exact (addressOf entry.overlappedResolved.base
    entry.overlappedSlot.range.start).isLt

theorem Entry.overlapped_byte_initialized_zero {state : Execution.State} {request : Request}
    (entry : Entry state request) (i : Fin 8) :
    entry.overlappedResolved.toResolvedAccess.cellAt?
      (entry.overlappedSlot.range.start + i.val) = some (0, true) :=
  entry.overlappedNull.2 i

/-- The actual register state fixes the handle across all compatible bindings. -/
theorem handle_unique {state : Execution.State} {left right : Request}
    (a : Entry state left) (b : Entry state right) : left.handle = right.handle := by
  exact a.handle.symm.trans b.handle

/-- The actual low R8 DWORD fixes the requested count across bindings. -/
theorem requested_unique {state : Execution.State} {left right : Request}
    (a : Entry state left) (b : Entry state right) : left.requested = right.requested := by
  rw [← a.requested_low, ← b.requested_low]

end Grass.Platform.Win32.WriteFile.Abi
