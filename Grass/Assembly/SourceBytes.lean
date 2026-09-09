import Grass.Assembly.SourceResolve
import Grass.Std.Logical.Vec

/-! Resolved source bytes reuse `ByteLayout.emitted`. `Result.bytes_length` and
`Result.decode_at_instruction` connect the emitted stream to the checked layout
and each origin's decoder evidence. Execution safety remains a separate proof. -/

namespace Grass.Assembly.ByteLayout

/-- Concatenating instruction lists concatenates their emitted bytes. -/
theorem emitted_append (before after : List Grass.ISA.X86.InsnEncoding) :
    emitted (before ++ after) = emitted before ++ emitted after := by
  simp [emitted]

/-- Dropping a computed prefix byte length leaves exactly the remaining instructions. -/
theorem emitted_drop_offset (instructions : List Grass.ISA.X86.InsnEncoding) (index : Nat) :
    (emitted instructions).drop (offset (sizes instructions) index) =
      emitted (instructions.drop index) := by
  have split := congrArg emitted (List.take_append_drop index instructions)
  rw [emitted_append] at split
  rw [← emitted_prefix_length instructions index, ← split]
  simp

end Grass.Assembly.ByteLayout

namespace Grass.Assembly.SourceResolve
open Grass.ISA.X86 Grass.Std.Logical

/-- Logical bytes of the resolved encodings, in their checked source traversal order. -/
def Result.bytes {frame rootOffset} (result : Result frame rootOffset) : Grass.Std.Logical.ByteArray :=
  Vec.fromList (ByteLayout.emitted result.encodings)

/-- Emitted length equals the size sum used to resolve every branch and RIP reference. -/
theorem Result.bytes_length {frame rootOffset} (result : Result frame rootOffset) :
    result.bytes.length = result.splice.finalSizes.sum := by
  simp only [Result.bytes, Vec.length_fromList, ByteLayout.emitted_length,
    ByteLayout.sizes, result.encoding_sizes]

/-- Each computed instruction boundary selects the exact emitted suffix. -/
theorem Result.bytes_at_instruction {frame rootOffset} (result : Result frame rootOffset)
    (index : Nat) :
    result.bytes.toList.drop (ByteLayout.offset result.splice.finalSizes index) =
      ByteLayout.emitted (result.encodings.drop index) := by
  change (ByteLayout.emitted result.encodings).drop _ = _
  rw [← result.encoding_sizes]
  exact ByteLayout.emitted_drop_offset _ _

/-- Traversal position is the stored origin index used by resolution evidence. -/
theorem Result.output_index_at {frame rootOffset} (result : Result frame rootOffset)
    (index : Nat) (bounded : index < result.outputs.length) :
    result.outputs[index].index = index := by
  have atIndex := congrArg (fun indices => indices[index]?) result.indicesExact
  have sourceBound : index < result.splice.outputs.length := by
    rw [← result.countExact]
    exact bounded
  simpa [List.getElem?_eq_getElem bounded, List.getElem?_range, sourceBound] using atIndex

/-- At every bounded instruction position, decoding recovers its resolved encoding
and the exact remaining byte stream. -/
theorem Result.decode_at_instruction {frame rootOffset} (result : Result frame rootOffset)
    (index : Nat) (bounded : index < result.outputs.length) :
    decodeInsn (result.bytes.toList.drop (ByteLayout.offset result.splice.finalSizes index)) =
      .ok (result.outputs[index].encoding,
        ByteLayout.emitted (result.encodings.drop (index + 1))) := by
  rw [result.bytes_at_instruction]
  have encodingBound : index < result.encodings.length := by
    simpa [Result.encodings] using bounded
  rw [List.drop_eq_getElem_cons encodingBound]
  change decodeInsn (result.encodings[index].toBytes ++ _) = _
  simp only [Result.encodings, List.getElem_map]
  exact result.outputs[index].encodingDecodes _

end Grass.Assembly.SourceResolve
