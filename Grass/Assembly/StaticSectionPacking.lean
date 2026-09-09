import Grass.Assembly.StaticObjects
import Grass.Artifact.PE.Layout

/-! Deterministic static packing and its structural guarantees, independent of PE placement. -/
namespace Grass.Assembly.StaticSection

open Grass.Artifact.PE Grass.Assembly.StaticObjects Grass.Std.Logical

structure Object where
  declaration : Declaration
  offset : Nat
deriving DecidableEq, Repr

def Object.endOffset (object : Object) : Nat :=
  object.offset + object.declaration.bytes.length

def packFrom (cursor : Nat) : List Declaration → List Object × Grass.Std.Logical.ByteArray
  | [] => ([], Vec.empty)
  | declaration :: tail =>
      let offset := alignUp cursor declaration.alignment
      let object := { declaration, offset }
      let packedTail := packFrom object.endOffset tail
      (object :: packedTail.1,
        Vec.replicate (offset - cursor) 0 ++ declaration.bytes ++ packedTail.2)

def ordered? : List Object → Bool
  | [] => true
  | object :: tail =>
      tail.all (fun later => decide (object.endOffset ≤ later.offset)) && ordered? tail

theorem packFrom_declarations (cursor : Nat) (declarations : List Declaration) :
    (packFrom cursor declarations).1.map Object.declaration = declarations := by
  induction declarations generalizing cursor with
  | nil => rfl
  | cons declaration tail ih =>
      simp only [packFrom, List.map_cons, List.cons.injEq, true_and]
      exact ih _

theorem packFrom_offsetsAligned (cursor : Nat) (declarations : List Declaration)
    (valid : ∀ declaration ∈ declarations, Nat.isPowerOfTwo declaration.alignment) :
    ∀ object ∈ (packFrom cursor declarations).1,
      object.offset % object.declaration.alignment = 0 := by
  induction declarations generalizing cursor with
  | nil => simp [packFrom]
  | cons declaration tail ih =>
      intro object member
      simp only [packFrom, List.mem_cons] at member
      rcases member with rfl | member
      · exact alignUp_mod_eq_zero _ (Nat.pos_of_isPowerOfTwo (valid _ List.mem_cons_self))
      · apply ih (alignUp cursor declaration.alignment + declaration.bytes.length)
          (fun later laterMember => valid later (List.mem_cons_of_mem declaration laterMember))
          object member

def packEnd (cursor : Nat) : List Declaration → Nat
  | [] => cursor
  | declaration :: tail =>
      packEnd (alignUp cursor declaration.alignment + declaration.bytes.length) tail

theorem cursor_le_packEnd (cursor : Nat) (declarations : List Declaration) :
    cursor ≤ packEnd cursor declarations := by
  induction declarations generalizing cursor with
  | nil => exact Nat.le_refl _
  | cons declaration tail ih =>
      exact Nat.le_trans (Nat.le_trans (le_alignUp _ _) (Nat.le_add_right _ _)) (ih _)

theorem packFrom_length (cursor : Nat) (declarations : List Declaration) :
    (packFrom cursor declarations).2.length = packEnd cursor declarations - cursor := by
  induction declarations generalizing cursor with
  | nil => simp [packFrom, packEnd]
  | cons declaration tail ih =>
      simp only [packFrom, packEnd]
      simp only [Object.endOffset, Vec.length_append, Vec.length_replicate]
      rw [ih]
      have h₁ := le_alignUp cursor declaration.alignment
      have h₂ := cursor_le_packEnd
        (alignUp cursor declaration.alignment + declaration.bytes.length) tail
      omega

theorem packFrom_offsets_ge (cursor : Nat) (declarations : List Declaration) :
    ∀ object ∈ (packFrom cursor declarations).1, cursor ≤ object.offset := by
  induction declarations generalizing cursor with
  | nil => simp [packFrom]
  | cons declaration tail ih =>
      intro object member
      simp only [packFrom, List.mem_cons] at member
      rcases member with rfl | member
      · exact le_alignUp _ _
      · exact Nat.le_trans (le_alignUp _ _) <|
          Nat.le_trans (Nat.le_add_right _ _) (ih _ object member)

theorem packFrom_ordered (cursor : Nat) (declarations : List Declaration) :
    ordered? (packFrom cursor declarations).1 = true := by
  induction declarations generalizing cursor with
  | nil => rfl
  | cons declaration tail ih =>
      simp only [packFrom, ordered?, Bool.and_eq_true]
      constructor
      · rw [List.all_eq_true]
        intro later member
        apply decide_eq_true
        simpa [Object.endOffset] using
          packFrom_offsets_ge
            (alignUp cursor declaration.alignment + declaration.bytes.length) tail later member
      · exact ih _

theorem packFrom_end_le_packEnd (cursor : Nat) (declarations : List Declaration) :
    ∀ object ∈ (packFrom cursor declarations).1,
      object.endOffset ≤ packEnd cursor declarations := by
  induction declarations generalizing cursor with
  | nil => simp [packFrom]
  | cons declaration tail ih =>
      intro object member
      simp only [packFrom, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [Object.endOffset]
        have := cursor_le_packEnd
          (alignUp cursor declaration.alignment + declaration.bytes.length) tail
        simpa [packEnd] using this
      · simpa [packEnd] using ih
          (alignUp cursor declaration.alignment + declaration.bytes.length) object member

theorem packFrom_contained (cursor : Nat) (declarations : List Declaration) :
    ∀ object ∈ (packFrom cursor declarations).1,
      object.endOffset - cursor ≤ (packFrom cursor declarations).2.length := by
  intro object member
  rw [packFrom_length]
  exact Nat.sub_le_sub_right (packFrom_end_le_packEnd cursor declarations object member) cursor

theorem packFrom_payload (cursor : Nat) (declarations : List Declaration) :
    ∀ object ∈ (packFrom cursor declarations).1,
      ((packFrom cursor declarations).2.drop (object.offset - cursor)).take
        object.declaration.bytes.length = object.declaration.bytes := by
  induction declarations generalizing cursor with
  | nil => simp [packFrom]
  | cons declaration tail ih =>
      intro object member
      simp only [packFrom, List.mem_cons] at member
      let offset := alignUp cursor declaration.alignment
      let next := offset + declaration.bytes.length
      let padding : Grass.Std.Logical.ByteArray := Vec.replicate (offset - cursor) 0
      rcases member with rfl | member
      · change ((padding ++ declaration.bytes ++ (packFrom next tail).2).drop
          (offset - cursor)).take declaration.bytes.length = declaration.bytes
        rw [Vec.append_assoc]
        have paddingLength : padding.length = offset - cursor := by simp [padding]
        rw [Vec.drop_append_of_length_eq paddingLength]
        simp
      · have objectStart := packFrom_offsets_ge next tail object member
        have offsetStart := le_alignUp cursor declaration.alignment
        have prefixLength : (padding ++ declaration.bytes).length = next - cursor := by
          simp only [Vec.length_append]
          simp [padding, next, offset]
          omega
        have indexSplit : object.offset - cursor =
            (next - cursor) + (object.offset - next) := by omega
        change ((padding ++ declaration.bytes ++ (packFrom next tail).2).drop
          (object.offset - cursor)).take object.declaration.bytes.length = _
        rw [indexSplit, ← Vec.drop_drop]
        rw [Vec.drop_append_of_length_eq prefixLength]
        exact ih next object member

theorem packFrom_zero_payloads (declarations : List Declaration) :
    ∀ object ∈ (packFrom 0 declarations).1,
      ((packFrom 0 declarations).2.drop object.offset).take
        object.declaration.bytes.length = object.declaration.bytes := by
  simpa using packFrom_payload 0 declarations

theorem packFrom_zero_payloads_all (declarations : List Declaration) :
    (packFrom 0 declarations).1.all (fun object => decide
      (((packFrom 0 declarations).2.drop object.offset).take
        object.declaration.bytes.length = object.declaration.bytes)) = true := by
  rw [List.all_eq_true]
  intro object member
  exact decide_eq_true (packFrom_zero_payloads declarations object member)

theorem packFrom_zero_contained_all (declarations : List Declaration) :
    (packFrom 0 declarations).1.all (fun object => decide
      (object.endOffset ≤ (packFrom 0 declarations).2.length)) = true := by
  rw [List.all_eq_true]
  intro object member
  exact decide_eq_true (by
    simpa using packFrom_contained 0 declarations object member)

theorem Table.packFrom_offsetsAligned_all (table : Table) :
    (packFrom 0 table.declarations).1.all (fun object => decide
      (object.offset % object.declaration.alignment = 0)) = true := by
  rw [List.all_eq_true]
  intro object member
  exact decide_eq_true <| packFrom_offsetsAligned 0 table.declarations
    (fun declaration declarationMember => table.alignment_valid declarationMember)
    object member

end Grass.Assembly.StaticSection
