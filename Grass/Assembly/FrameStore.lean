import Grass.Assembly.SourceFrame

/-! Typed source-store resolution using the exact frame's slot environment.
`resolve?_source` connects the source occurrence, operand, and derived slot map.
There is no second parser for stack declarations in this path. -/
namespace Grass.Assembly.FrameStore

open X86ControlFlow

def resolve? (frame : SourceFrame.Result) (rspRootOffset : Nat) (item : CodeItem) :
    Option Store32.Resolved := do
  if ¬ item ∈ frame.program.collected.code then none else do
  match item.instruction.mnemonic, item.instruction.operands with
  | .mov, [.symbol slot, .immediate value] =>
    if value < 2 ^ 32 then
      Store32.resolve? frame.layout rspRootOffset (SourceStore.slotEnv frame.slots)
        ⟨slot, BitVec.ofNat 32 value⟩
    else none
  | _, _ => none

theorem resolve?_source {frame : SourceFrame.Result} {rspRootOffset : Nat} {item : CodeItem}
    {resolved : Store32.Resolved} (success : resolve? frame rspRootOffset item = some resolved) :
    item ∈ frame.program.collected.code ∧
      ∃ slot value,
        item.instruction.mnemonic = .mov ∧
        item.instruction.operands = [.symbol slot, .immediate value] ∧
        value < 2 ^ 32 ∧
        Store32.resolve? frame.layout rspRootOffset (SourceStore.slotEnv frame.slots)
          ⟨slot, BitVec.ofNat 32 value⟩ = some resolved := by
  unfold resolve? at success
  split at success
  · contradiction
  · rename_i member
    refine ⟨by simpa using member, ?_⟩
    split at success
    · rename_i slot value hm ho
      split at success
      · rename_i bounded
        exact ⟨slot, value, hm, ho, bounded, success⟩
      · contradiction
    · contradiction

theorem resolve?_range_in_frame {frame : SourceFrame.Result} {rspRootOffset : Nat}
    {item : CodeItem} {resolved : Store32.Resolved}
    (success : resolve? frame rspRootOffset item = some resolved) :
    (frame.layout.frameRange.shift rspRootOffset).Contains resolved.range := by
  obtain ⟨_, _, _, _, _, _, primitive⟩ := resolve?_source success
  exact Store32.range_in_frame_of_resolve? primitive

theorem resolve?_encoding_decodes {frame : SourceFrame.Result} {rspRootOffset : Nat}
    {item : CodeItem} {resolved : Store32.Resolved}
    (success : resolve? frame rspRootOffset item = some resolved)
    (rest : Grass.Std.Logical.ByteSeq) :
    Grass.ISA.X86.decodeInsn (resolved.encoding.toBytes ++ rest) =
      .ok (resolved.encoding, rest) := by
  obtain ⟨_, _, _, _, _, _, primitive⟩ := resolve?_source success
  exact Store32.encoding_decodes_of_resolve? primitive rest

end Grass.Assembly.FrameStore
