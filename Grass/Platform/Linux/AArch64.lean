import Grass.Platform.Linux.Syscall
import Grass.ISA.AArch64.Source
import Grass.Artifact.Binary.EndianLaws

/-! # Linux interpretation of an exact AArch64 source request

The selected emitted form is SVC #0. Rejecting another immediate here restricts
this source profile; it is not a claim that Linux rejects every other immediate.
The checked source word and CPU are retained. Fetch, exception-level admission,
CheckForSVCTrap, Linux routing and provider completion remain separate obligations.
-/

namespace Grass.Platform.Linux.Syscall.AArch64
open Grass.ISA.AArch64 Grass.Std.Logical Grass.Artifact.Binary

/-- Project the ABI registers from the same CPU used by the source receipt. -/
def captureRequest (before : Cpu) : Captured :=
  captureAArch64 {
    x8 := before.gpr ⟨8, by decide⟩
    x0 := before.gpr ⟨0, by decide⟩
    x1 := before.gpr ⟨1, by decide⟩
    x2 := before.gpr ⟨2, by decide⟩ }

/-- A checked interpretation, not a native syscall-entry receipt. -/
structure DecodedRequest {bytes : Grass.Std.Logical.ByteArray}
    (source : SourceWord bytes) (before : Cpu) where
  instruction : SupervisorCall.Request source.word before
  immediateZero : instruction.immediate = 0
  request : Syscall.Request
  decoded : Syscall.decode? .aarch64 (captureRequest before) = some request

/-- Derive the instruction and request from the exact source/CPU, with no
caller-supplied syscall identity, register snapshot or result. -/
def decode? {bytes : Grass.Std.Logical.ByteArray} (source : SourceWord bytes)
    (before : Cpu) : Option (DecodedRequest source before) := do
  let instruction ← SupervisorCall.request? source.word before
  if zero : instruction.immediate = 0 then
    match decoded : Syscall.decode? .aarch64 (captureRequest before) with
    | none => none
    | some request => some ⟨instruction, zero, request, decoded⟩
  else none

/-- Every accepted interpretation retains the exact SVC #0 source prefix and
the exact unconsumed bytes from the shared endian parser. -/
theorem DecodedRequest.source_exact {bytes : Grass.Std.Logical.ByteArray}
    {source : SourceWord bytes} {before : Cpu} (result : DecodedRequest source before) :
    bytes = emitWord (SupervisorCall.encode 0) ++ source.rest := by
  have word := result.instruction.source_exact
  rw [result.immediateZero] at word
  have consumed := takeLittleEndian_done source.parsed
  simpa only [emitWord, ← word] using consumed

theorem DecodedRequest.number_exact {bytes : Grass.Std.Logical.ByteArray}
    {source : SourceWord bytes} {before : Cpu} (result : DecodedRequest source before) :
    (BitVec.setWidth 32 (before.gpr ⟨8, by decide⟩)).toNat =
      number .aarch64 result.request.id :=
  decode?_number result.decoded

/-- Register access on the ISA request and the Linux projection names the same
CPU; no independently chosen register view can replace it. -/
theorem DecodedRequest.arguments_exact {bytes : Grass.Std.Logical.ByteArray}
    {source : SourceWord bytes} {before : Cpu} (result : DecodedRequest source before) :
    (captureRequest before).arg0 = result.instruction.register ⟨0, by decide⟩ ∧
    (captureRequest before).arg1 = result.instruction.register ⟨1, by decide⟩ ∧
    (captureRequest before).arg2 = result.instruction.register ⟨2, by decide⟩ :=
  ⟨rfl, rfl, rfl⟩

end Grass.Platform.Linux.Syscall.AArch64
