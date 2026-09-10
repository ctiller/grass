import Grass.ISA.X86.Execution.State
import Grass.Platform.Linux.Syscall

/-!
# Linux x86-64 syscall register projection

This adapter connects the shared Linux syscall decoder to the repository's
actual x86 execution-state representation. It is a state projection only: a
separate ISA receipt must prove that execution reached a `SYSCALL` boundary and
which before/after state is applicable.
-/

namespace Grass.Platform.Linux.Syscall.X86

open Grass.ISA.X86 Grass.ISA.X86.Execution

/-- Capture the native request registers from the actual architectural state. -/
def captureRequest (state : State) : Captured :=
  captureX86 {
    rax := state.gpr .rax
    rdi := state.gpr .rdi
    rsi := state.gpr .rsi
    rdx := state.gpr .rdx }

/-- Decode a native x86-64 request from the actual architectural state. -/
def decodeRequest? (state : State) : Option Request :=
  decode? .x86_64 (captureRequest state)

/-- Classify the raw kernel return register in an actual post-entry state. -/
def decodeResult (state : State) : RawResult :=
  decodeRaw (state.gpr .rax)

@[simp] theorem captureRequest_number (state : State) :
    (captureRequest state).number = BitVec.setWidth 32 (state.gpr .rax) := rfl

@[simp] theorem captureRequest_arguments (state : State) :
    (captureRequest state).arg0 = state.gpr .rdi ∧
    (captureRequest state).arg1 = state.gpr .rsi ∧
    (captureRequest state).arg2 = state.gpr .rdx := by
  exact ⟨rfl, rfl, rfl⟩

/-- Successful state decoding fixes EAX to the selected native table number. -/
theorem decodeRequest?_number {state : State} {request : Request}
    (decoded : decodeRequest? state = some request) :
    (BitVec.setWidth 32 (state.gpr .rax)).toNat = number .x86_64 request.id :=
  decode?_number decoded

@[simp] theorem decodeResult_eq (state : State) :
    decodeResult state = decodeRaw (state.gpr .rax) := rfl

end Grass.Platform.Linux.Syscall.X86
