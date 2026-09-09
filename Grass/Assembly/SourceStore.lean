import Grass.Assembly.SourceInput
import Grass.Assembly.Store32

/-!
# Selected source-store resolution

This adapter resolves an individual retained source line. It does not lower the
surrounding body. The bounded stack declaration parser admits only UInt32 locals;
their declaration order determines offsets within the computed local region.
`resolveLine?_source` records the source occurrence and the resolver equation.
-/

namespace Grass.Assembly.SourceStore

open Grass.ABI.Win64 Grass.Core Grass.ISA.X86 Grass.Std.Logical
open SourceInput

/-- Four bytes per admitted UInt32 declaration, in declaration order. -/
def slotEnv (slots : List String) : Store32.SlotEnv :=
  ⟨slots.zipIdx.map fun (name, index) => (name, index * 4)⟩

/-- Source declarations supply local geometry; call arguments and saved registers
remain inputs from the enclosing function's lowering. -/
def frameForSlots (argumentCount : Nat) (savedRegisters : List Gpr)
    (slots : List String) : CallFrameLayout :=
  { argumentCount := argumentCount, localBytes := slots.length * 4,
    localAlignment := 4, savedRegisters := savedRegisters }

theorem frameForSlots_localBytes (argumentCount : Nat) (savedRegisters : List Gpr)
    (slots : List String) :
    (frameForSlots argumentCount savedRegisters slots).localBytes = slots.length * 4 := rfl

def resolveLine? (layout : CallFrameLayout) (rspRootOffset : Nat)
    (body : Body) (line : SourceLine) : Option Store32.Resolved := do
  let slots ← uint32StackSlots body
  if ¬ slots.Nodup then none else do
  if layout.localBytes != slots.length * 4 then none else do
  if ¬ line ∈ body.lines then none else do
  match line.parsed with
  | .symbolicStore slot value =>
    if value < 2 ^ 32 then
      Store32.resolve? layout rspRootOffset (slotEnv slots) ⟨slot, BitVec.ofNat 32 value⟩
    else none
  | _ => none

theorem resolveLine?_source {layout : CallFrameLayout} {rspRootOffset : Nat}
    {body : Body} {line : SourceLine} {resolved : Store32.Resolved}
    (h : resolveLine? layout rspRootOffset body line = some resolved) :
    ∃ slots slot value,
      uint32StackSlots body = some slots ∧ slots.Nodup ∧
      layout.localBytes = slots.length * 4 ∧ line ∈ body.lines ∧
      line.parsed = .symbolicStore slot value ∧ value < 2 ^ 32 ∧
      Store32.resolve? layout rspRootOffset (slotEnv slots)
        ⟨slot, BitVec.ofNat 32 value⟩ = some resolved := by
  cases hs : uint32StackSlots body with
  | none => simp [resolveLine?, hs] at h
  | some slots =>
    by_cases hn : slots.Nodup
    · by_cases hl : layout.localBytes = slots.length * 4
      · by_cases hm : line ∈ body.lines
        · cases hp : line.parsed with
          | blank => simp [resolveLine?, hs, hl, hm, hp] at h
          | label name => simp [resolveLine?, hs, hl, hm, hp] at h
          | unsupported => simp [resolveLine?, hs, hl, hm, hp] at h
          | symbolicStore slot value =>
            by_cases hv : value < 2 ^ 32
            · simp [resolveLine?, hs, hn, hl, hm, hp, hv] at h
              exact ⟨slots, slot, value, rfl, hn, hl, hm, rfl, hv, h⟩
            · simp [resolveLine?, hs, hl, hm, hp, hv] at h
        · simp [resolveLine?, hs, hl, hm] at h
      · simp [resolveLine?, hs, hn, hl] at h
    · simp [resolveLine?, hs, hn] at h
theorem resolveLine?_writeBytes {layout : CallFrameLayout} {rspRootOffset : Nat}
    {body : Body} {line : SourceLine} {resolved : Store32.Resolved}
    (h : resolveLine? layout rspRootOffset body line = some resolved) :
    ∃ slot value, line.parsed = .symbolicStore slot value ∧ value < 2 ^ 32 ∧
      resolved.writeBytes = le32 (BitVec.ofNat 32 value) := by
  obtain ⟨_, slot, value, _, _, _, _, hp, hv, hr⟩ := resolveLine?_source h
  exact ⟨slot, value, hp, hv, Store32.writeBytes_of_resolve? hr⟩

theorem resolveLine?_range_in_frame {layout : CallFrameLayout} {rspRootOffset : Nat}
    {body : Body} {line : SourceLine} {resolved : Store32.Resolved}
    (h : resolveLine? layout rspRootOffset body line = some resolved) :
    (layout.frameRange.shift rspRootOffset).Contains resolved.range := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hr⟩ := resolveLine?_source h
  exact Store32.range_in_frame_of_resolve? hr

theorem resolveLine?_encoding_decodes {layout : CallFrameLayout} {rspRootOffset : Nat}
    {body : Body} {line : SourceLine} {resolved : Store32.Resolved}
    (h : resolveLine? layout rspRootOffset body line = some resolved)
    (rest : ByteSeq) :
    decodeInsn (resolved.encoding.toBytes ++ rest) = .ok (resolved.encoding, rest) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hr⟩ := resolveLine?_source h
  exact Store32.encoding_decodes_of_resolve? hr rest

end Grass.Assembly.SourceStore
