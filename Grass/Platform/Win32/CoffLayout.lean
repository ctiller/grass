import Grass.Platform.Win32.Coff

/-!
# COFF object layout

`Coff.lean` says what each record looks like. This says where they go.

## The bug this exists to make unwritable

A section header carries `pointerToRawData` and `pointerToRelocations`, two file
offsets a writer computes and a reader trusts. Nothing about the record type
stops a writer from filling them in with numbers that point somewhere else --
they are `BitVec 32` like every other field, and an object file with a section
header pointing four bytes past its own data is a well-formed COFF file that
describes something that is not there.

That is the interesting failure, because it is invisible to every check that
looks at one record at a time. `Coff.lean`'s theorems say a section header is
forty bytes and a relocation is ten; neither says the numbers *inside* the
header agree with where the writer actually put anything.

So the offsets are not a field a caller fills in here. `Section` has no offset
fields at all; `Object.toBytes` lays the file out and `Object.sectionHeaders`
derives every offset from that same layout, so there is nothing for a caller to
get wrong.

It takes two theorems, and the difference between them is worth keeping.

`data_at_layout_offset` proves the layout half: reading a section's length from
the offset the layout assigns it returns exactly that section's bytes. That
theorem is stated over the computed offset, and it is *not* enough on its own --
changing `pointerToRawData` to `dOff + 1` leaves it provable, which was checked
by making the change. A file whose every header misaddressed its section would
pass it.

`header_points_at_data` closes that. It reads the offset and the length out of
the emitted `SectionHeader` rather than recomputing them, so the field is what
the theorem is about. All three field mutations tried against it fail: an
off-by-one `pointerToRawData`, an oversized `sizeOfRawData`, and a
`pointerToRelocations` aimed at the data.

Its two hypotheses are the wrap conditions, and they are real rather than
bookkeeping. `pointerToRawData` and `sizeOfRawData` are thirty-two bits, so an
object with more than four gigabytes before a section cannot address it and
COFF has no wider field to offer. Stating them as hypotheses rather than
assuming them is what keeps the theorem true of the format instead of true of
small examples.

## The shape of an object file

Twenty bytes of file header, then forty bytes per section header, then each
section's raw data in order, then each section's relocation directory in order.
Data before relocations, all sections' data first, is a choice: the format
permits any arrangement the pointers describe, and `ml64` interleaves them per
section. Nothing here depends on matching that, and
`Tests/Platform/Win32/CoffFixture.lean` checks records rather than arrangement,
so this is a layout that is *a* valid COFF file, not a reproduction of a
particular assembler's.

## Not modelled

No symbol table, so `pointerToSymbolTable` is zero and the object cannot be
linked. That is the next piece of work, and until it exists this writes a file
that is structurally valid and semantically incomplete -- which is why nothing
here claims to emit a linkable object.
-/

namespace Grass.Platform.Win32.Coff

open Grass.Std.Logical (ByteSeq)

/--
A section as an author supplies it: what it is called, what is in it, and what
must be fixed up. Deliberately carries no file offsets.
-/
structure Section where
  /-- The eight-byte name. -/
  name : SectionName
  /-- The section's contents. -/
  data : ByteSeq
  /-- Fix-ups into `data`. -/
  relocations : List Relocation
  /-- Section flags. -/
  characteristics : BitVec 32

/-- Bytes the relocation directory occupies. -/
def Section.relocationSize (s : Section) : Nat := 10 * s.relocations.length

/-- The relocation directory, flattened. -/
def Section.relocationBytes (s : Section) : ByteSeq :=
  (s.relocations.map Relocation.toBytes).flatten

/-- **Flattened relocations are ten bytes per entry.**

Stated over a plain list rather than over a `Section`, because the induction has
to generalise and a field of a fixed structure does not. -/
theorem length_flatten_relocations (rs : List Relocation) :
    ((rs.map Relocation.toBytes).flatten).length = 10 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rest ih => simp [ih]; omega

/-- **The directory is exactly `relocationSize` bytes.**

No separators, which is what makes `pointerToRelocations` plus
`numberOfRelocations` sufficient for a reader to find every entry. -/
@[simp] theorem Section.length_relocationBytes (s : Section) :
    s.relocationBytes.length = s.relocationSize :=
  length_flatten_relocations s.relocations

/-- An object file: a machine and its sections. -/
structure Object where
  /-- Target machine. -/
  machine : Machine
  /-- The sections, in file order. -/
  sections : List Section

/-- Bytes before the first section's data: the file header and the table. -/
def Object.headerSize (o : Object) : Nat := 20 + 40 * o.sections.length

/--
Where each section's raw data starts, in order.

A running total rather than an index computation, because the sections have
different sizes and a closed form would have to be kept in step with
`toBytes` by hand -- which is the coupling this module exists to remove.
-/
def dataOffsets (start : Nat) : List Section → List Nat
  | [] => []
  | s :: rest => start :: dataOffsets (start + s.data.length) rest

/-- Total size of every section's raw data. -/
def Object.dataSize (o : Object) : Nat :=
  (o.sections.map (fun s => s.data.length)).sum

/-- Where each section's relocation directory starts, in order. -/
def relocOffsets (start : Nat) : List Section → List Nat
  | [] => []
  | s :: rest => start :: relocOffsets (start + s.relocationSize) rest

/-- **There is one data offset per section.** -/
@[simp] theorem length_dataOffsets (start : Nat) (ss : List Section) :
    (dataOffsets start ss).length = ss.length := by
  induction ss generalizing start with
  | nil => rfl
  | cons s rest ih => simp [dataOffsets, ih]

/-- **There is one relocation offset per section.** -/
@[simp] theorem length_relocOffsets (start : Nat) (ss : List Section) :
    (relocOffsets start ss).length = ss.length := by
  induction ss generalizing start with
  | nil => rfl
  | cons s rest ih => simp [relocOffsets, ih]

/--
**Every data offset is at or past where the layout starts.**

The statement that a section's contents never land inside the header table,
which is the corruption a wrong `headerSize` would produce. -/
theorem dataOffsets_ge (start : Nat) (ss : List Section) :
    ∀ off ∈ dataOffsets start ss, start ≤ off := by
  induction ss generalizing start with
  | nil => simp [dataOffsets]
  | cons s rest ih =>
      intro off h
      simp [dataOffsets] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_add_right _ _) (ih _ off h)


/-! ## Laying the file out -/

/-- Total size of every relocation directory. -/
def Object.relocSize (o : Object) : Nat :=
  (o.sections.map Section.relocationSize).sum

/-- The file header. No symbol table, so those two fields are zero. -/
def Object.fileHeader (o : Object) : FileHeader where
  machine := o.machine
  numberOfSections := BitVec.ofNat 16 o.sections.length
  timeDateStamp := 0
  pointerToSymbolTable := 0
  numberOfSymbols := 0
  sizeOfOptionalHeader := 0
  characteristics := 0

/--
The section table, with every offset derived from the layout.

The two pointer fields are computed here and nowhere else. That is the whole
mechanism: a caller supplies a `Section`, which has no offset fields, so there
is no way to supply a wrong one. -/
def Object.sectionHeaders (o : Object) : List SectionHeader :=
  (o.sections.zip (dataOffsets o.headerSize o.sections)).zip
      (relocOffsets (o.headerSize + o.dataSize) o.sections)
    |>.map fun ((s, dOff), rOff) =>
      { name := s.name
        virtualSize := 0
        virtualAddress := 0
        sizeOfRawData := BitVec.ofNat 32 s.data.length
        pointerToRawData := BitVec.ofNat 32 dOff
        pointerToRelocations := BitVec.ofNat 32 rOff
        pointerToLinenumbers := 0
        numberOfRelocations := BitVec.ofNat 16 s.relocations.length
        numberOfLinenumbers := 0
        characteristics := s.characteristics }

/--
The object file.

File header, section table, all raw data, all relocation directories. -/
def Object.toBytes (o : Object) : ByteSeq :=
  o.fileHeader.toBytes
    ++ (o.sectionHeaders.map SectionHeader.toBytes).flatten
    ++ (o.sections.map Section.data).flatten
    ++ (o.sections.map Section.relocationBytes).flatten

/-- **Flattened section headers are forty bytes each.** -/
theorem length_flatten_sectionHeaders (hs : List SectionHeader) :
    ((hs.map SectionHeader.toBytes).flatten).length = 40 * hs.length := by
  induction hs with
  | nil => rfl
  | cons h rest ih => simp [ih]; omega

/-- **There is one section header per section.** -/
@[simp] theorem Object.length_sectionHeaders (o : Object) :
    o.sectionHeaders.length = o.sections.length := by
  simp [sectionHeaders, headerSize]

/-- **Flattened section data is `dataSize` bytes.** -/
theorem length_flatten_data (ss : List Section) :
    ((ss.map Section.data).flatten).length
      = (ss.map (fun s => s.data.length)).sum := by
  induction ss with
  | nil => rfl
  | cons s rest ih => simp [ih]

/-- **Flattened relocation directories are `relocSize` bytes.** -/
theorem length_flatten_relocBytes (ss : List Section) :
    ((ss.map Section.relocationBytes).flatten).length
      = (ss.map Section.relocationSize).sum := by
  induction ss with
  | nil => rfl
  | cons s rest ih => simp [ih]

/--
**The file is exactly header, data and relocations, and nothing else.**

No padding and no slack. This is what makes the offsets in the section table
mean what a reader assumes, and it is the theorem that fails first if a future
alignment requirement is added to `toBytes` without being added here. -/
theorem Object.length_toBytes (o : Object) :
    o.toBytes.length = o.headerSize + o.dataSize + o.relocSize := by
  rw [toBytes, List.length_append, List.length_append, List.length_append,
      FileHeader.length_toBytes, length_flatten_sectionHeaders,
      length_flatten_data, length_flatten_relocBytes,
      Object.length_sectionHeaders]
  simp [headerSize, dataSize, relocSize]

/-! ## The pointers point at the data -/

/-- **The file header and section table together are exactly `headerSize`
bytes.**

The fact every offset in the section table is measured from. -/
theorem Object.length_prefix (o : Object) :
    (o.fileHeader.toBytes
      ++ (o.sectionHeaders.map SectionHeader.toBytes).flatten).length
      = o.headerSize := by
  rw [List.length_append, FileHeader.length_toBytes,
      length_flatten_sectionHeaders, Object.length_sectionHeaders]
  simp [headerSize]

/-- Dropping a known-length prefix and `k` more leaves the rest dropped by `k`. -/
theorem drop_length_append (a b : ByteSeq) (k : Nat) :
    (a ++ b).drop (a.length + k) = b.drop k := by
  induction a with
  | nil => simp
  | cons x rest ih =>
      simp only [List.length_cons, List.cons_append]
      rw [show rest.length + 1 + k = (rest.length + k) + 1 by omega,
          List.drop_succ_cons]
      exact ih

/--
**Reading a section's length at the offset the layout assigns it returns that
section.**

Stated by decomposing `sections` at the section of interest rather than by
index, because the offset is a sum over everything before it and a
decomposition carries that sum directly.

The offset here is the computed one, not `SectionHeader.pointerToRawData`:
mutating the field to `dOff + 1` leaves this theorem provable. That is why it is
not the module's headline result -- `header_points_at_data` reads the offset out
of the emitted header and does catch it. This one is the layout fact the other
one rests on. -/
theorem Object.data_at_layout_offset (o : Object) (pre : List Section)
    (sec : Section) (post : List Section)
    (h : o.sections = pre ++ sec :: post) :
    ((o.toBytes.drop
        (o.headerSize + (pre.map (fun x => x.data.length)).sum)).take
      sec.data.length) = sec.data := by
  have hpre := o.length_prefix
  have hdata : (o.sections.map Section.data).flatten
      = (pre.map Section.data).flatten
        ++ (sec.data ++ (post.map Section.data).flatten) := by
    rw [h]; simp
  have hk : ((pre.map Section.data).flatten).length
      = (pre.map (fun x => x.data.length)).sum := length_flatten_data pre
  rw [toBytes, List.append_assoc, ← hpre, drop_length_append, hdata,
      List.append_assoc, ← hk, List.drop_left, List.append_assoc,
      List.take_left]

/-! ## Tying the header field to the layout -/

/-- **Offsets for a concatenation split at the concatenation point.**

The enabling lemma: it says the offsets computed for `post` are exactly the
offsets computed from a start advanced by everything `pre` occupies, which is
what lets a decomposition of `sections` name the offset of the section it
decomposes at. -/
theorem dataOffsets_append (start : Nat) (pre post : List Section) :
    dataOffsets start (pre ++ post)
      = dataOffsets start pre
        ++ dataOffsets (start + (pre.map (fun x => x.data.length)).sum) post := by
  induction pre generalizing start with
  | nil => simp [dataOffsets]
  | cons x rest ih =>
      simp only [List.cons_append, dataOffsets, List.map_cons, List.sum_cons,
                 List.cons_append, ih]
      rw [show start + x.data.length + (rest.map (fun y => y.data.length)).sum
            = start + (x.data.length + (rest.map (fun y => y.data.length)).sum)
          by omega]

/-- **Relocation offsets split the same way.** -/
theorem relocOffsets_append (start : Nat) (pre post : List Section) :
    relocOffsets start (pre ++ post)
      = relocOffsets start pre
        ++ relocOffsets (start + (pre.map Section.relocationSize).sum) post := by
  induction pre generalizing start with
  | nil => simp [relocOffsets]
  | cons x rest ih =>
      simp only [List.cons_append, relocOffsets, List.map_cons, List.sum_cons,
                 List.cons_append, ih]
      rw [show start + x.relocationSize + (rest.map Section.relocationSize).sum
            = start + (x.relocationSize + (rest.map Section.relocationSize).sum)
          by omega]

/--
**The section table carries a header whose `pointerToRawData` and
`sizeOfRawData` really do address that section's bytes.**

The obligation the module header recorded, discharged. This is the statement
`data_at_layout_offset` could not make: the offset is read out of the emitted
header rather than recomputed, so a header field that disagreed with the layout
would falsify it. Mutating `pointerToRawData` to `dOff + 1` breaks this theorem,
where it leaves `data_at_layout_offset` provable.

The two bounds are the wrap conditions, and they are real rather than
bookkeeping: `pointerToRawData` is thirty-two bits, so an object file with more
than four gigabytes before a section cannot address it, and COFF has no larger
field to offer. A writer that exceeded them would emit a file whose headers
point into their own low bits. -/
theorem Object.header_points_at_data (o : Object) (pre : List Section)
    (sec : Section) (post : List Section)
    (h : o.sections = pre ++ sec :: post)
    (hoff : o.headerSize + (pre.map (fun x => x.data.length)).sum < 2 ^ 32)
    (hlen : sec.data.length < 2 ^ 32) :
    ∃ hdr ∈ o.sectionHeaders,
      hdr.name = sec.name
      ∧ (o.toBytes.drop hdr.pointerToRawData.toNat).take hdr.sizeOfRawData.toNat
          = sec.data := by
  refine ⟨{ name := sec.name
            virtualSize := 0
            virtualAddress := 0
            sizeOfRawData := BitVec.ofNat 32 sec.data.length
            pointerToRawData :=
              BitVec.ofNat 32
                (o.headerSize + (pre.map (fun x => x.data.length)).sum)
            pointerToRelocations :=
              BitVec.ofNat 32
                (o.headerSize + o.dataSize
                  + (pre.map Section.relocationSize).sum)
            pointerToLinenumbers := 0
            numberOfRelocations := BitVec.ofNat 16 sec.relocations.length
            numberOfLinenumbers := 0
            characteristics := sec.characteristics }, ?_, rfl, ?_⟩
  · unfold Object.sectionHeaders
    rw [h, dataOffsets_append, relocOffsets_append,
        List.zip_append (by simp), List.zip_append (by simp)]
    simp [dataOffsets, relocOffsets]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hlen]
    exact o.data_at_layout_offset pre sec post h

end Grass.Platform.Win32.Coff



