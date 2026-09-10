import Grass.Platform.Win32.WriteFilePrepare
import Grass.Platform.Win32.WriteFileHandoff
import Tests.Platform.Win32WriteFileStackPlan

/-!
# Checked WriteFile request preparation

The positive case consumes an actual checked CALL result and canonical supplied
arguments from the stack-plan fixture. Mutated CPU states below isolate
preparation checks; they are not additional CALL or native execution receipts.
-/

namespace Grass.Tests.Win32WriteFilePrepare

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Tests.Win32WriteFileStackPlan

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def result := EntryFactory.prepare? called.result request.buffer request.countSlot
  request.bytes fifthArgument

theorem actual_call_prepares : result.toOption.isSome := by decide

def preparedEntry := result.toOption.get (by decide)

def generatedRequest :=
  EntryFactory.requestOf called.result request.buffer request.countSlot request.bytes

def planned := Abi.StackPlanFactory.deriveLoaded? binding preparedEntry

theorem prepared_entry_reaches_stack_plan : planned.toOption.isSome := by decide

def protocol : CallProtocol.State ApiRequest :=
  CallProtocol.initial called.result.machine FreshSupply.initial (by decide)

def before : ExecutionState.State ApiRequest :=
  ExecutionState.State.ofCallProtocol protocol called.result rfl (.caller inputs.thread)

def handed := WriteFile.entryHandoff? before generatedRequest
  (planned.toOption.get (by decide)) inputs.independentContext

theorem prepared_request_reaches_protocol_entry : handed.isSome := by decide

def handoff := handed.get (by decide)

theorem recorded_count_is_supplied_canonical_count :
    (WriteFile.EntryHandoff.record handoff).request.countSlot = request.countSlot := rfl

theorem canonical_count_retained :
    (EntryFactory.requestOf called.result request.buffer request.countSlot request.bytes).countSlot =
      request.countSlot := rfl

theorem canonical_buffer_retained :
    (EntryFactory.requestOf called.result request.buffer request.countSlot request.bytes).buffer =
      request.buffer := rfl

theorem payload_retained :
    (EntryFactory.requestOf called.result request.buffer request.countSlot request.bytes).bytes =
      request.bytes := rfl

theorem handle_from_actual_rcx :
    (EntryFactory.requestOf called.result request.buffer request.countSlot request.bytes).handle =
      called.result.gpr .rcx := rfl

theorem requested_from_actual_low_r8 :
    (EntryFactory.requestOf called.result request.buffer request.countSlot request.bytes).requested =
      BitVec.setWidth 32 (called.result.gpr .r8) := rfl

def wrongCountState : Execution.State :=
  { called.result with gpr := fun register =>
      if register = .r9 then called.result.gpr .r9 + 1 else called.result.gpr register }

theorem mismatched_count_address_refuses :
    (match EntryFactory.prepare? wrongCountState request.buffer request.countSlot request.bytes
      fifthArgument with | .error .countAddress => true | _ => false) = true := by decide

def wrongBufferState : Execution.State :=
  { called.result with gpr := fun register =>
      if register = .rdx then called.result.gpr .rdx + 1 else called.result.gpr register }

theorem mismatched_buffer_address_refuses :
    (match EntryFactory.prepare? wrongBufferState request.buffer request.countSlot request.bytes
      fifthArgument with | .error .bufferAddress => true | _ => false) = true := by decide

theorem wrong_payload_refuses :
    (match EntryFactory.prepare? called.result request.buffer request.countSlot
      (.fromList [11, 22, 34]) fifthArgument with | .error .input => true | _ => false) = true := by decide

theorem wrong_payload_size_refuses :
    (EntryFactory.prepare? called.result request.buffer request.countSlot
      (.fromList [11, 22]) fifthArgument).toOption.isNone := by decide

theorem wrong_buffer_size_refuses :
    (EntryFactory.prepare? called.result
      { request.buffer with range := ⟨0, 2⟩ } request.countSlot request.bytes
      fifthArgument).toOption.isNone := by decide

theorem wrong_count_size_refuses :
    (EntryFactory.prepare? called.result request.buffer
      { request.countSlot with range := ⟨16, 3⟩ } request.bytes
      fifthArgument).toOption.isNone := by decide

theorem wrong_fifth_slot_refuses :
    (EntryFactory.prepare? called.result request.buffer request.countSlot request.bytes
      request.countSlot).toOption.isNone := by decide

def highR8State : Execution.State :=
  { called.result with gpr := fun register =>
      if register = .r8 then 0x100000003 else called.result.gpr register }

theorem requested_uses_low_dword :
    (EntryFactory.prepare? highR8State request.buffer request.countSlot request.bytes
      fifthArgument).toOption.isSome := by decide

def uninitializedBuffer : Argument := { request.buffer with range := ⟨32, 3⟩ }

def uninitializedBufferState : Execution.State :=
  { called.result with gpr := fun register =>
      if register = .rdx then called.result.gpr .rdx + 32 else called.result.gpr register }

theorem uninitialized_payload_refuses :
    (match EntryFactory.prepare? uninitializedBufferState uninitializedBuffer request.countSlot
      request.bytes fifthArgument with | .error .input => true | _ => false) = true := by decide

def overlappingCount : Argument := { request.countSlot with range := ⟨0, 4⟩ }

def overlappingCountState : Execution.State :=
  { called.result with gpr := fun register =>
      if register = .r9 then called.result.gpr .rdx else called.result.gpr register }

theorem overlapping_buffer_count_refuses :
    (match EntryFactory.prepare? overlappingCountState request.buffer overlappingCount
      request.bytes fifthArgument with | .error .bufferCountOverlap => true | _ => false) = true := by decide

def uninitializedFifth : Argument := { fifthArgument with range := ⟨208, 8⟩ }

def uninitializedFifthState : Execution.State :=
  { called.result with gpr := fun register =>
      if register = .rsp then called.result.gpr .rsp + 8 else called.result.gpr register }

theorem uninitialized_fifth_refuses :
    (match EntryFactory.prepare? uninitializedFifthState request.buffer request.countSlot
      request.bytes uninitializedFifth with | .error .fifthNull => true | _ => false) = true := by decide

def nonzeroFifth : Argument := { fifthArgument with range := ⟨160, 8⟩ }

def nonzeroFifthState : Execution.State :=
  { called.result with gpr := fun register =>
      if register = .rsp then called.result.gpr .rsp - 40 else called.result.gpr register }

theorem initialized_nonzero_fifth_refuses :
    (match EntryFactory.prepare? nonzeroFifthState request.buffer request.countSlot
      request.bytes nonzeroFifth with | .error .fifthNull => true | _ => false) = true := by decide

theorem mismatched_provenance_space_refuses :
    (EntryFactory.prepare? called.result
      { request.buffer with provenance := { request.buffer.provenance with space := .cpuPhysical } }
      request.countSlot request.bytes fifthArgument).toOption.isNone := by decide

/- This isolated placement makes a wrapping bit-vector RSP+40 equal the
supplied fifth address. The producer must still reject the natural sum. -/
def lowPlacementMemory? : Option MemoryState := do
  let allocation ← called.result.machine.memory.allocations.lookup inputs.stack.allocation
  let backing ← called.result.machine.memory.backings.lookup allocation.backing
  let installed ← MemoryState.empty.installBacking? allocation.backing
    { backing with bytes := backing.bytes.write 8 (List.replicate 8 0) true }
  installed.allocate? inputs.stack.allocation { allocation with base := some 0 }

def lowPlacementMemory := lowPlacementMemory?.get (by decide)

def overflowRspState : Execution.State :=
  { called.result with
    machine := { called.result.machine with memory := lowPlacementMemory }
    gpr := fun register =>
      if register = .rsp then 0xffffffffffffffe0
      else if register = .rdx then 0
      else if register = .r9 then 16
      else called.result.gpr register }

def lowFifth : Argument := { fifthArgument with range := ⟨8, 8⟩ }

theorem wrapping_address_would_match_as_bitvector :
    overflowRspState.gpr .rsp + BitVec.ofNat 64 Abi.overlappedSlotOffset = 8 := by decide

theorem wrapping_fifth_address_refuses :
    (match EntryFactory.prepare? overflowRspState request.buffer request.countSlot request.bytes
      lowFifth with | .error .fifthAddress => true | _ => false) = true := by decide

end Grass.Tests.Win32WriteFilePrepare
