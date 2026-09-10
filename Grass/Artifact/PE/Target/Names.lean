/-!
# ASCII names in a PE32+ image

A section's `Name` field, an imported symbol's hint/name record and a DLL name
string all carry the same thing: an ASCII, NUL-free byte string, terminated or
padded by NUL. This module is the one encoder/decoder pair for that, with the
round trip both the section table and the import directory need.

Format authority: Microsoft, PE Format
(<https://learn.microsoft.com/en-us/windows/win32/debug/pe-format>), sections
"Section Table (Section Headers)" (`Name`) and "Hint/Name Table".
-/

namespace Grass.Artifact.PE

/-- One ASCII character as a name byte. -/
def nameByte (c : Char) : UInt8 := UInt8.ofNat c.toNat

/-- One name byte back as a character. -/
def nameChar (b : UInt8) : Char := Char.ofNat b.toNat

/-- What a PE name field can carry: ASCII, and no NUL, which is every such
field's own terminator or padding. -/
def AsciiName (s : String) : Prop := ∀ c ∈ s.toList, 0 < c.toNat ∧ c.toNat < 128

instance : DecidablePred AsciiName := fun s =>
  inferInstanceAs (Decidable (∀ c ∈ s.toList, 0 < c.toNat ∧ c.toNat < 128))

/-- A name's bytes, without terminator or padding. -/
def nameBytes (s : String) : List UInt8 := s.toList.map nameByte

@[simp] theorem length_nameBytes (s : String) : (nameBytes s).length = s.toList.length := by
  simp [nameBytes]

/-- The name a byte string spells. -/
def decodeName (bytes : List UInt8) : String := String.ofList (bytes.map nameChar)

/-- An ASCII, NUL-free character never encodes to a zero byte, so it never
collides with a terminator or with padding. -/
theorem nameByte_ne_zero {c : Char} (ascii : 0 < c.toNat ∧ c.toNat < 128) : nameByte c ≠ 0 := by
  intro zero
  have digits : (nameByte c).toNat = 0 := by rw [zero]; rfl
  rw [nameByte, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at digits
  omega

/-- No byte of an ASCII, NUL-free name is zero. -/
theorem nameBytes_ne_zero {s : String} (ascii : AsciiName s) : ∀ b ∈ nameBytes s, b ≠ 0 := by
  intro b member
  obtain ⟨c, memberC, rfl⟩ := List.mem_map.mp member
  exact nameByte_ne_zero (ascii c memberC)

/-- Encoding and decoding a name round-trip for every name a PE name field can
carry. -/
theorem decodeName_nameBytes {s : String} (ascii : AsciiName s) : decodeName (nameBytes s) = s := by
  have chars : s.toList.map (nameChar ∘ nameByte) = s.toList.map id :=
    List.map_congr_left fun c memberC => by
      have bound := (ascii c memberC).2
      simp only [Function.comp_apply, nameChar, nameByte, id]
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Char.ofNat_toNat]
  rw [decodeName, nameBytes, List.map_map, chars, List.map_id, String.ofList_toList]

/-- Padding stops at the first NUL, so a NUL-free prefix is recovered exactly.
This is the section-table `Name` field's rule. -/
theorem takeWhile_append_replicate {xs : List UInt8} (nonzero : ∀ b ∈ xs, b ≠ 0) (count : Nat) :
    (xs ++ List.replicate count 0).takeWhile (fun b => b != 0) = xs := by
  induction xs with
  | nil =>
      cases count with
      | zero => rfl
      | succ n => simp [List.replicate]
  | cons x xs ih =>
      have head : x ≠ 0 := nonzero x (List.mem_cons_self ..)
      have tail : ∀ b ∈ xs, b ≠ 0 := fun b member => nonzero b (List.mem_cons_of_mem _ member)
      simp [head, ih tail]

/-- Consume a NUL-terminated byte string. This is the hint/name and DLL-name
rule. -/
def parseCString : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
      if b = 0 then some ([], rest)
      else
        match parseCString rest with
        | none => none
        | some (taken, tail) => some (b :: taken, tail)

/-- A NUL-free byte string followed by its terminator is recovered exactly,
with the exact byte suffix. -/
theorem parseCString_append {xs : List UInt8} (nonzero : ∀ b ∈ xs, b ≠ 0) (rest : List UInt8) :
    parseCString (xs ++ 0 :: rest) = some (xs, rest) := by
  induction xs with
  | nil => simp [parseCString]
  | cons x xs ih =>
      have head : x ≠ 0 := nonzero x (List.mem_cons_self ..)
      have tail : ∀ b ∈ xs, b ≠ 0 := fun b member => nonzero b (List.mem_cons_of_mem _ member)
      simp [parseCString, head, ih tail]

end Grass.Artifact.PE
