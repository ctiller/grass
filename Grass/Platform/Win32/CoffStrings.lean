import Grass.Platform.Win32.CoffSymbol

/-!
# The COFF string table

Where a symbol name too long for its eight-byte field actually lives.

`CoffSymbol.lean` gives `SymbolName.long` an offset into this table and says
nothing about what is there. That is the gap this closes: an offset is only
meaningful if reading at it returns the name it was issued for, and nothing so
far made that true.

## The size field describes itself

The table opens with a four-byte size, and that size *includes those four
bytes*. An empty table is therefore four bytes reading `04 00 00 00`, not zero
bytes and not four zero bytes. Getting this wrong by four is not a rounding
error: a reader uses the field to find the end of the table and hence the end of
the object, so an off-by-four either truncates the last name or runs past the
file. `size_counts_itself` states it, and `emptyTable_bytes` pins the empty
case, which is the one a writer is most likely to special-case wrongly.

## Offsets start at four, so zero is never a name

The first name begins immediately after the size field, at offset four. Offset
zero addresses the size field itself and can never be a name -- which is
precisely why `SymbolName.short?` refuses a field of four zero bytes: such a
field is read as a long-form reference to offset zero, and offset zero is not a
string. The two rules are the same rule seen from opposite ends, and
`stringOffsets_ge_four` is this end of it.

## Not modelled

Deduplication. Two symbols with the same name get two entries here, which is
wasteful and entirely legal. A real linker's table interns them, and a future
version that does will have to keep `name_at_offset` true of the shared entry
rather than of a per-symbol one.
-/

namespace Grass.Platform.Win32.Coff

open Grass.ISA.X86 (le32)
open Grass.Std.Logical (ByteSeq)

/-- One entry: the name, then a terminating NUL. -/
def stringEntry (name : ByteSeq) : ByteSeq := name ++ [0]

/-- **An entry is one byte longer than the name.** -/
@[simp] theorem length_stringEntry (name : ByteSeq) :
    (stringEntry name).length = name.length + 1 := by simp [stringEntry]

/-- All entries, concatenated. -/
def stringEntries (names : List ByteSeq) : ByteSeq :=
  (names.map stringEntry).flatten

/-- The bytes every entry occupies. -/
def stringEntriesSize (names : List ByteSeq) : Nat :=
  (names.map (fun n => n.length + 1)).sum

/-- **The concatenated entries are `stringEntriesSize` bytes.** -/
@[simp] theorem length_stringEntries (names : List ByteSeq) :
    (stringEntries names).length = stringEntriesSize names := by
  induction names with
  | nil => rfl
  | cons n rest ih => simp [stringEntries, stringEntriesSize] at *; omega

/--
The table: a four-byte self-inclusive size, then the entries.

The four is not a magic number appearing twice by coincidence -- it is the
width of the size field, and it is why `stringOffsets_ge_four` holds. -/
def stringTableBytes (names : List ByteSeq) : ByteSeq :=
  le32 (BitVec.ofNat 32 (4 + stringEntriesSize names)) ++ stringEntries names

/-- **The table is four bytes longer than its entries.** -/
@[simp] theorem length_stringTableBytes (names : List ByteSeq) :
    (stringTableBytes names).length = 4 + stringEntriesSize names := by
  simp [stringTableBytes]

/--
**The size field counts itself.**

The whole content of the field, and the off-by-four a writer is most likely to
make. A reader adds this number to the table's start to find the end of the
object; if it counted only the entries, the last name would be truncated. -/
theorem size_counts_itself (names : List ByteSeq) :
    ((stringTableBytes names).take 4)
      = le32 (BitVec.ofNat 32 (stringTableBytes names).length) := by
  rw [length_stringTableBytes]
  simp [stringTableBytes, le32]

/--
**An empty table is four bytes, not zero.**

The case a writer special-cases wrongly, stated concretely so the general
theorem above cannot be satisfied vacuously. -/
theorem emptyTable_bytes : stringTableBytes [] = [0x04, 0x00, 0x00, 0x00] := by
  decide

/-- Where each name starts, in order. -/
def stringOffsets (start : Nat) : List ByteSeq → List Nat
  | [] => []
  | n :: rest => start :: stringOffsets (start + n.length + 1) rest

/-- **There is one string offset per name.** -/
@[simp] theorem length_stringOffsets (start : Nat) (names : List ByteSeq) :
    (stringOffsets start names).length = names.length := by
  induction names generalizing start with
  | nil => rfl
  | cons n rest ih => simp [stringOffsets, ih]
/-- **Every offset is at least four, so none of them is offset zero.**

Offset zero addresses the size field. A symbol whose name field is four zero
bytes is read as a reference to offset zero, which is why `SymbolName.short?`
refuses such a field: this theorem is the other end of that rule, saying there
is nothing there to refer to. -/
theorem stringOffsets_ge_four (names : List ByteSeq) :
    ∀ off ∈ stringOffsets 4 names, 4 ≤ off := by
  have general : ∀ (start : Nat) (ns : List ByteSeq),
      ∀ off ∈ stringOffsets start ns, start ≤ off := by
    intro start ns
    induction ns generalizing start with
    | nil => simp [stringOffsets]
    | cons n rest ih =>
        intro off hoff
        simp [stringOffsets] at hoff
        rcases hoff with rfl | hoff
        · exact Nat.le_refl _
        · exact Nat.le_trans (by omega) (ih _ off hoff)
  exact general 4 names

/-- **Offsets split at a concatenation, exactly as section offsets do.** -/
theorem stringOffsets_append (start : Nat) (pre post : List ByteSeq) :
    stringOffsets start (pre ++ post)
      = stringOffsets start pre
        ++ stringOffsets (start + stringEntriesSize pre) post := by
  induction pre generalizing start with
  | nil => simp [stringOffsets, stringEntriesSize]
  | cons x rest ih =>
      simp only [List.cons_append, stringOffsets, ih, stringEntriesSize,
                 List.map_cons, List.sum_cons]
      rw [show start + x.length + 1 + (rest.map (fun n => n.length + 1)).sum
            = start + (x.length + 1 + (rest.map (fun n => n.length + 1)).sum)
          by omega]

/--
**Reading at the offset a name was issued returns that name.**

The theorem the whole module is for: `SymbolName.long` carries an offset, and
this says the offset means something. Without it a long-form symbol name is a
number with no stated relationship to any string in the file.

Stated by decomposing the name list, the same way `data_at_layout_offset`
decomposes sections, because the offset is a sum over everything before it. -/
theorem name_at_offset (pre : List ByteSeq) (nm : ByteSeq)
    (post : List ByteSeq) :
    (((stringTableBytes (pre ++ nm :: post)).drop
        (4 + stringEntriesSize pre)).take nm.length) = nm := by
  have hentries : stringEntries (pre ++ nm :: post)
      = stringEntries pre ++ (stringEntry nm ++ stringEntries post) := by
    simp [stringEntries]
  have hpfx : (le32 (BitVec.ofNat 32
        (4 + stringEntriesSize (pre ++ nm :: post))) ++ stringEntries pre).length
      = 4 + stringEntriesSize pre := by simp
  rw [stringTableBytes, hentries, ← List.append_assoc, ← hpfx, List.drop_left,
      stringEntry, List.append_assoc, List.take_left]

/--
**The offset issued to a name is the offset that name is read back at.**

`stringOffsets` hands out offsets and `name_at_offset` reads at
`4 + stringEntriesSize pre`; nothing so far said those were the same number, and
a module whose issuing and reading disagree is worse than one that does neither.
This is the link, and it is why `stringOffsets_append` exists.

The pattern is the one `CoffLayout.lean` needed twice: a definition that assigns
offsets and a theorem that reads at them are two different things until
something states they agree. -/
theorem stringOffsets_decompose (pre : List ByteSeq) (nm : ByteSeq)
    (post : List ByteSeq) :
    stringOffsets 4 (pre ++ nm :: post)
      = stringOffsets 4 pre
        ++ (4 + stringEntriesSize pre)
           :: stringOffsets (4 + stringEntriesSize pre + nm.length + 1) post := by
  rw [stringOffsets_append]
  rfl

/--
**Reading at the issued offset returns the name it was issued for.**

`name_at_offset` and `stringOffsets` composed: the offset in the table's own
offset list, at the position of `nm`, is where `nm`'s bytes are. This is what a
`SymbolName.long` carrying that offset actually promises. -/
theorem name_at_issued_offset (pre : List ByteSeq) (nm : ByteSeq)
    (post : List ByteSeq) :
    ∃ off ∈ stringOffsets 4 (pre ++ nm :: post),
      ((stringTableBytes (pre ++ nm :: post)).drop off).take nm.length = nm := by
  refine ⟨4 + stringEntriesSize pre, ?_, name_at_offset pre nm post⟩
  rw [stringOffsets_decompose]
  simp
end Grass.Platform.Win32.Coff
