import Grass.Platform.Win32.Coff
import Grass.Platform.Win32.CoffSymbol
import Grass.Platform.Win32.CoffStrings

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

Twenty bytes of file header, then forty bytes per section header, then every
section's raw data, then every section's relocation directory, then the symbol
table, then the string table.

That order is a choice and not a requirement. The format locates each part by a
pointer -- `pointerToRawData`, `pointerToRelocations`, `pointerToSymbolTable`,
and the string table by following the symbol table -- so any arrangement the
headers describe is legal, and `ml64` interleaves data and relocations per
section instead. Nothing here depends on matching it, and
`Tests/Platform/Win32/CoffFixture.lean` checks records rather than arrangement.
This is *a* valid COFF file, not a reproduction of a particular assembler's.

## Not modelled

Auxiliary symbol records. Five of the fifteen symbols in the measured object
declare `numberOfAuxSymbols = 1` and are followed by a record this profile does
not emit, so an object written here with such a count would mis-index every
symbol after it. `Symbol.toBytes` writes the field; nothing writes the record.

Alignment. Sections are laid end to end with no padding, which
`Object.length_toBytes` states exactly. Real toolchains align section data, and
a version that does will have to add the padding to `toBytes` and to that
theorem together -- which is what makes it the theorem that fails first if only
one of them is changed.
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

/-- An object file: a machine, its sections, and its two tables. -/
structure Object where
  /-- Target machine. -/
  machine : Machine
  /-- The sections, in file order. -/
  sections : List Section
  /-- The symbol table, in index order. A relocation's `symbolIndex` is an
  index into this list. -/
  symbols : List Symbol
  /-- The string table's names, in order, each without its terminator. A
  `SymbolName.long` offset addresses one of these. -/
  strings : List ByteSeq

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

/-- Where the symbol table starts: after every section's data and relocations. -/
def Object.symbolTableOffset (o : Object) : Nat :=
  o.headerSize + o.dataSize + o.relocSize

/-- The file header, with both symbol-table fields derived from the layout. -/
def Object.fileHeader (o : Object) : FileHeader where
  machine := o.machine
  numberOfSections := BitVec.ofNat 16 o.sections.length
  timeDateStamp := 0
  pointerToSymbolTable := BitVec.ofNat 32 o.symbolTableOffset
  numberOfSymbols := BitVec.ofNat 32 o.symbols.length
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

/-- Everything after the section data: relocations, symbols, strings. -/
def Object.tailBytes (o : Object) : ByteSeq :=
  (o.sections.map Section.relocationBytes).flatten
    ++ (o.symbols.map Symbol.toBytes).flatten
    ++ stringTableBytes o.strings

/--
The object file.

Grouped as `(header ++ table) ++ (data ++ tail)` rather than left to
`++`'s associativity, and that is deliberate. Every offset theorem below reads
at some point past the first group and inside the second, so this grouping is
the shape those proofs need. Written flat, adding anything to the tail --
which is exactly what the symbol and string tables were -- reassociates the
whole expression and breaks proofs that have nothing to do with the change. -/
def Object.toBytes (o : Object) : ByteSeq :=
  (o.fileHeader.toBytes ++ (o.sectionHeaders.map SectionHeader.toBytes).flatten)
    ++ ((o.sections.map Section.data).flatten ++ o.tailBytes)

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

/-- **Flattened symbol records are eighteen bytes each.** -/
theorem length_flatten_symbols (ss : List Symbol) :
    ((ss.map Symbol.toBytes).flatten).length = 18 * ss.length := by
  induction ss with
  | nil => rfl
  | cons x rest ih => simp [ih]; omega

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
    o.toBytes.length
      = o.headerSize + o.dataSize + o.relocSize
        + 18 * o.symbols.length + (4 + stringEntriesSize o.strings) := by
  rw [toBytes, List.length_append, List.length_append, List.length_append,
      FileHeader.length_toBytes, length_flatten_sectionHeaders,
      length_flatten_data, Object.length_sectionHeaders, tailBytes,
      List.length_append, List.length_append, length_flatten_relocBytes,
      length_flatten_symbols, length_stringTableBytes]
  simp [headerSize, dataSize, relocSize]
  omega

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
  rw [toBytes, ← hpre, drop_length_append, hdata,
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

/-! ## The symbol table is where the file header says it is -/

/--
**Reading at the layout's symbol-table offset returns the symbol records.**

The layout half, the same shape as `data_at_layout_offset`: stated over the
computed offset rather than over `FileHeader.pointerToSymbolTable`, and not
sufficient on its own for the same reason. -/
theorem Object.symbols_at_layout_offset (o : Object) :
    ((o.toBytes.drop o.symbolTableOffset).take (18 * o.symbols.length))
      = (o.symbols.map Symbol.toBytes).flatten := by
  have hpre := o.length_prefix
  have hdata : ((o.sections.map Section.data).flatten).length = o.dataSize :=
    length_flatten_data o.sections
  have hrel : ((o.sections.map Section.relocationBytes).flatten).length
      = o.relocSize := length_flatten_relocBytes o.sections
  have hsym : ((o.symbols.map Symbol.toBytes).flatten).length
      = 18 * o.symbols.length := length_flatten_symbols o.symbols
  rw [toBytes, symbolTableOffset, ← hpre, ← hdata, ← hrel, Nat.add_assoc,
      drop_length_append, drop_length_append, tailBytes, List.append_assoc,
      List.drop_left, ← hsym, List.take_left]

/--
**The symbol table is at `pointerToSymbolTable`, and there are
`numberOfSymbols` of them.**

The field half. The offset is read out of the emitted file header rather than
recomputed, so a header field that disagreed with the layout falsifies it --
which is the distinction `data_at_layout_offset` could not make and
`header_points_at_data` had to be written to close.

This is the third time the pattern has come up: a definition assigns an offset,
a theorem reads at one, and nothing connects them until something says so. The
bound is the wrap condition, and `numberOfSymbols` needs its own because it is a
separate field with a separate width. -/
theorem Object.symbol_table_at_header_pointer (o : Object)
    (hoff : o.symbolTableOffset < 2 ^ 32)
    (hcount : o.symbols.length < 2 ^ 32) :
    ((o.toBytes.drop o.fileHeader.pointerToSymbolTable.toNat).take
        (18 * o.fileHeader.numberOfSymbols.toNat))
      = (o.symbols.map Symbol.toBytes).flatten := by
  show ((o.toBytes.drop (BitVec.ofNat 32 o.symbolTableOffset).toNat).take
      (18 * (BitVec.ofNat 32 o.symbols.length).toNat)) = _
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hcount]
  exact o.symbols_at_layout_offset

/-! ## The header's counts describe the file -/

/--
**`numberOfSections` is the number of section headers actually written.**

A reader takes this field and reads that many forty-byte records; the field is
how it knows where the table ends and the data begins. Nothing else here
constrained it -- setting it to zero left every other theorem in this module
provable, which a mutation demonstrated, and would produce a file whose sections
a reader simply never finds.

The bound is the field's width. More than 65535 sections cannot be counted, and
a writer past that limit would report the count modulo 2^16. -/
theorem Object.numberOfSections_correct (o : Object)
    (h : o.sections.length < 2 ^ 16) :
    o.fileHeader.numberOfSections.toNat = o.sectionHeaders.length := by
  show (BitVec.ofNat 16 o.sections.length).toNat = _
  rw [Object.length_sectionHeaders]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/--
**The section table really is at `sectionTableOffset`.**

`FileHeader.sectionTableOffset` is twenty plus whatever `sizeOfOptionalHeader`
claims, and a reader trusts it to find the first section header. This says the
headers are there.

It also ties the optional-header field to the layout: `toBytes` writes no
optional header, so a nonzero `sizeOfOptionalHeader` would move the computed
offset past the table's real start and this would fail. -/
theorem Object.section_table_at_offset (o : Object) :
    ((o.toBytes.drop o.fileHeader.sectionTableOffset).take
        (40 * o.sections.length))
      = (o.sectionHeaders.map SectionHeader.toBytes).flatten := by
  have hfh : o.fileHeader.toBytes.length = 20 := FileHeader.length_toBytes _
  have hsh : ((o.sectionHeaders.map SectionHeader.toBytes).flatten).length
      = 40 * o.sections.length := by
    rw [length_flatten_sectionHeaders, Object.length_sectionHeaders]
  rw [toBytes,
      show o.fileHeader.sectionTableOffset = o.fileHeader.toBytes.length + 0
        from by simp [FileHeader.sectionTableOffset, Object.fileHeader],
      List.append_assoc, drop_length_append, List.drop_zero, ← hsh,
      List.take_left]

end Grass.Platform.Win32.Coff



