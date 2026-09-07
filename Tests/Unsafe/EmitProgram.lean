import Grass.Unsafe.EmitProgram

/-!
# Tainted lowered-program emission fixtures

The fixture pins block/source retention, consecutive offsets including a
zero-byte instruction, exact byte concatenation, and mandatory taint order.
-/

namespace Grass.Tests.Unsafe.EmitProgram

open Grass Grass.CFG Grass.Construct.Fragment Grass.Construct.Source Grass.Unsafe

private structure Instruction where
  payload : List UInt8
deriving Repr, DecidableEq

private def blockId (name : String) : BlockId :=
  ⟨⟨"test.unsafe.emit-program", name⟩⟩
private def generatorId : FragmentId :=
  ⟨⟨"test.unsafe.emit-program", "wrapper"⟩⟩

private def first : Instruction := ⟨[0x10, 0x11]⟩
private def empty : Instruction := ⟨[]⟩
private def last : Instruction := ⟨[0x20]⟩

private def graph : Graph Unit Unit := ⟨blockId "entry", []⟩

private def program : LoweredProgram Unit Unit Instruction where
  graph := graph
  items := [
    ⟨blockId "entry", ⟨[generatorId], [], 0⟩, first⟩,
    ⟨blockId "entry", ⟨[generatorId], [], 1⟩, empty⟩,
    ⟨blockId "finish", ⟨[], [], 0⟩, last⟩]

private def encoder : RawEncoder Instruction := ⟨Instruction.payload⟩
private def primary : Taint :=
  ⟨.externalGenerator, "raw program encoder is unverified"⟩
private def override : Taint :=
  ⟨.userOverride, "inspection output only"⟩

private def emission : RawProgramEmission Unit Unit Instruction :=
  emitRawProgram program encoder primary [override]

example : emission.graph = program.graph := rfl
example : emission.items.map (fun item => item.lowered.block) =
    [blockId "entry", blockId "entry", blockId "finish"] := rfl
example : emission.items.map (fun item => item.lowered.origin) =
    [⟨[generatorId], [], 0⟩, ⟨[generatorId], [], 1⟩, ⟨[], [], 0⟩] := rfl
example : emission.items.map RawProgramEncodedInstruction.offset = [0, 2, 2] := rfl
example : ConsecutiveProgramOffsets 0 emission.items :=
  emitRawProgram.offsetsExact program encoder primary [override]
example : emission.bytes = [0x10, 0x11, 0x20] := rfl
example : emission.byteLength = 3 := rfl
example : emission.items.map (fun item => item.lowered.instruction) =
    [first, empty, last] :=
  emitRawProgram.instructionsExact program encoder primary [override]
example : emission.taints = [primary, override] :=
  emitRawProgram.taintsExact program encoder primary [override]
example : emission.taints ≠ [] := emission.taints_ne_nil

end Grass.Tests.Unsafe.EmitProgram
