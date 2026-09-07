import Grass.Unsafe.Emit

/-!
# Tainted raw hierarchy emission fixtures

The fixture pins structural origins, consecutive offsets including a zero-byte
instruction, exact byte concatenation, exact instruction projection, and the
mandatory ordered taint ledger.
-/

namespace Grass.Tests.Unsafe.Emit

open Grass Grass.Construct.Fragment Grass.Unsafe

private structure Instruction where
  payload : List UInt8
deriving Repr, DecidableEq

private def generatorId : FragmentId := ⟨⟨"test.unsafe.emit", "wrapper"⟩⟩

private def first : Instruction := ⟨[0x10, 0x11]⟩
private def empty : Instruction := ⟨[]⟩
private def last : Instruction := ⟨[0x20]⟩

private def source : Source Instruction :=
  .generated generatorId
    (.append (.literal [first]) (.literal [empty, last]))

private def encoder : RawEncoder Instruction := ⟨Instruction.payload⟩

private def primary : Taint :=
  ⟨.externalGenerator, "raw encoder has no semantic certificate"⟩
private def override : Taint :=
  ⟨.userOverride, "emit for inspection only"⟩

private def emission : RawEmission Instruction :=
  emitRaw source encoder primary [override]

example : emission.items.map (fun item => item.located.instruction) =
    [first, empty, last] :=
  emitRaw.instructionsExact source encoder primary [override]

example : emission.items.map RawEncodedInstruction.offset = [0, 2, 2] := rfl
example : ConsecutiveOffsets 0 emission.items :=
  emitRaw.offsetsExact source encoder primary [override]
example : emission.items.map RawEncodedInstruction.bytes =
    [[0x10, 0x11], [], [0x20]] := rfl
example : emission.bytes = [0x10, 0x11, 0x20] := rfl
example : emission.byteLength = 3 := rfl

example : emission.items.map RawEncodedInstruction.located =
    source.expandLocated :=
  emitRaw.locationsExact source encoder primary [override]

example : emission.bytes =
    source.expandLocated.flatMap (fun item => encoder.encode item.instruction) :=
  emitRaw.bytesExact source encoder primary [override]

example : emission.taints = [primary, override] :=
  emitRaw.taintsExact source encoder primary [override]
example : emission.taints ≠ [] := emission.taints_ne_nil

end Grass.Tests.Unsafe.Emit
