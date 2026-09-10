import Grass.Platform.Linux.Syscall
import Grass.ISA.AArch64.Control

/-! # Linux interpretation of an exact AArch64 source request

The selected emitted form is SVC #0. Rejecting another immediate here restricts
this source profile; it is not a claim that Linux rejects every other immediate.
The existing ISA request and its CPU are retained. Fetch, exception-level admission,
CheckForSVCTrap, Linux routing and provider completion remain separate obligations.
-/

namespace Grass.Platform.Linux.Syscall.AArch64
open Grass.ISA.AArch64

/-- Project the ABI registers from the same CPU used by the source receipt. -/
def captureRequest (before : Cpu) : Captured :=
  captureAArch64 {
    x8 := before.gpr ⟨8, by decide⟩
    x0 := before.gpr ⟨0, by decide⟩
    x1 := before.gpr ⟨1, by decide⟩
    x2 := before.gpr ⟨2, by decide⟩ }

/-- A checked interpretation, not a native syscall-entry receipt. -/
structure DecodedRequest {word : BitVec 32} {before : Cpu}
    (instruction : SupervisorCall.Request word before) where
  immediateZero : instruction.immediate = 0
  request : Syscall.Request
  decoded : Syscall.decode? .aarch64 (captureRequest before) = some request

/-- Interpret the existing ISA request directly. Instruction decoding belongs
to the ISA producer; Linux adds only its selected immediate and ABI conversion. -/
def decode? {word : BitVec 32} {before : Cpu}
    (instruction : SupervisorCall.Request word before) : Option (DecodedRequest instruction) :=
  if zero : instruction.immediate = 0 then
    match decoded : Syscall.decode? .aarch64 (captureRequest before) with
    | none => none
    | some request => some ⟨zero, request, decoded⟩
  else none

theorem DecodedRequest.number_exact {word : BitVec 32} {before : Cpu}
    {instruction : SupervisorCall.Request word before} (result : DecodedRequest instruction) :
    (BitVec.setWidth 32 (before.gpr ⟨8, by decide⟩)).toNat =
      number .aarch64 result.request.id :=
  decode?_number result.decoded

/-- Register access on the ISA request and the Linux projection names the same
CPU; no independently chosen register view can replace it. -/
theorem DecodedRequest.arguments_exact {word : BitVec 32} {before : Cpu}
    {instruction : SupervisorCall.Request word before} (_ : DecodedRequest instruction) :
    (captureRequest before).arg0 = instruction.register ⟨0, by decide⟩ ∧
    (captureRequest before).arg1 = instruction.register ⟨1, by decide⟩ ∧
    (captureRequest before).arg2 = instruction.register ⟨2, by decide⟩ :=
  ⟨rfl, rfl, rfl⟩

end Grass.Platform.Linux.Syscall.AArch64
