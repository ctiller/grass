import Grass.ISA.X86.Bytes

/-!
# COFF object structure

The three fixed-size records a Win64 object file is made of: the file header,
the section table, and the relocation entries. This is what `emitProgram` has
to write around the instruction bytes `Grass/ISA/X86/Bytes.lean` produces, and
what any differential has to read to find them again.

## Why this is modelled rather than parsed in a script

A Python reader of these structures existed and was deleted. It held about
forty-five lines of COFF layout -- the forty-byte section header, the ten-byte
relocation, the offsets of `PointerToRelocations` and `NumberOfRelocations` --
as unverified constants in `struct.unpack_from` calls, and it lived in a tree
this agent does not own. Both problems have the same fix. The emitter needs a
COFF *writer* regardless, so the format is modelled once here, in Lean, instead
of twice with one copy unchecked.

## What an object file cannot tell you, and why it matters here

Every address in a `.obj` is an unresolved relocation. The four bytes a field
will occupy read zero until a linker fills them, so a reader that compares
section *contents* cannot distinguish a writer that emitted three fields in the
right order from one that emitted them in any other order, or omitted one: all
of them produce the same zeros.

The relocation directory is what carries that structure, and it needs no linker.
This was measured rather than assumed, against `ml64` output: a single function
produces exactly three `ADDR32NB` relocations into `.pdata`, at offsets 0, 4 and
8, and the addend stored at offset 4 -- `EndAddress` -- is the function's length.
`Grass/ABI/Win64/UnwindBytes.lean` records the rest of that measurement.

So `Relocation` is not an accessory to this model. It is the only part of an
object file that states layout in a form a reader can check, which is why it is
here rather than deferred until something needs to emit one.

## Scope

The seam decision is `g-build:3`, which puts generic typed format algebra and
streaming parser and writer machinery with `g-build`, and x86 encoding and
decoding facts with `c-x86`.

This paragraph cited `g-build:4` for that, which is wrong and was found by
`g-design:212`'s sibling finding. `g-build:4` is a request to `g-foundation` to
add an import to `Tools/AxiomAudit.lean`; it decides nothing about ownership.
`g-build:3` is the one addressed to this agent and stating the split.

This module is the encoding-facts side: the records, their field order, and
their byte lengths. It builds no parser combinators and offers no generic
serialization interface.

**That scope claim is contested and the contest is the live question here.**
`g-design:173` reads this family as a second object-file library rather than
encoding facts, because `Grass.Artifact.COFF` is being built by its registered
owner and these are distinct Lean types with no bridge between them. Under that
reading the container records, placement, symbols, whole-object serialization
and validation belong to `Artifact`, and what stays here is the x86-specific
relocation meaning reached through an adapter. That is not settled and is not
this module's to settle alone; see `g-design:173` for what it asks for.

This module is deliberately **not** re-exported from `Grass/Platform/Win32.lean`.
That facade is, in its own words, "the public facade for the Win32 API family",
and an object file format is not part of that family -- it is what the emitter
writes, not something an author calls. Adding it would widen a cone
`Tests/Facade/Containment.lean` checks, for a module no author of Win32 API code
needs. An author who needs COFF imports it directly. If `g-design` reads
decision 134 as covering the format too, that is their call and this paragraph
is the place it was decided otherwise.

Only what an object file needs is modelled. The optional header, the symbol
table, string table, line numbers and every image-only field are absent -- not
deferred behind a placeholder, simply not here, so that nothing reads as
supported when it is not.
-/

namespace Grass.Platform.Win32.Coff

open Grass.ISA.X86 (le16 le32)
open Grass.Std.Logical (ByteSeq)

/-! ## Machine type -/

/--
The target machine.

One constructor, because `docs/DECISIONS.md` 16 fixes this profile to Win32 x64
and a machine field that could hold `i386` would be a field this project has no
way to be right about.
-/
inductive Machine where
  /-- `IMAGE_FILE_MACHINE_AMD64`. -/
  | amd64
deriving DecidableEq, Repr, Inhabited

/-- The sixteen-bit code written into the file header. -/
def Machine.code : Machine → BitVec 16
  | .amd64 => 0x8664

/-! ## Relocations -/

/--
The relocation kinds this profile emits.

`addr32nb` is the one every structure in `Grass/ABI/Win64/**` needs: an
image-relative 32-bit address, which is how `UNWIND_INFO`'s handler field and
all three `RUNTIME_FUNCTION` fields are stored. `addr64` and `rel32` are here
because instruction operands need them and leaving them out would push a caller
towards a raw `BitVec 16`.
-/
inductive RelocationType where
  /-- `IMAGE_REL_AMD64_ADDR64`: a 64-bit virtual address. -/
  | addr64
  /-- `IMAGE_REL_AMD64_ADDR32NB`: a 32-bit image-relative address. -/
  | addr32nb
  /-- `IMAGE_REL_AMD64_REL32`: 32-bit relative, with the displacement field
  ending the instruction. -/
  | rel32
  /-- `REL32_1` through `REL32_5`: 32-bit relative, with `trailing` bytes of
  the instruction following the displacement field. The parameter is bounded by
  `RelocationType.ripRelative?`, which is the only way to build one. -/
  | rel32Trailing (trailing : Nat)
deriving DecidableEq, Repr, Inhabited

/--
The sixteen-bit type code.

The `REL32` family is consecutive: `REL32` is 4 and `REL32_n` is `4 + n`. That
is not a coincidence worth exploiting silently -- `ripRelative_code` states
it, and `ripRelative?` is what keeps `trailing` in the range where it holds. -/
def RelocationType.code : RelocationType → BitVec 16
  | .addr64 => 0x0001
  | .addr32nb => 0x0003
  | .rel32 => 0x0004
  | .rel32Trailing n => BitVec.ofNat 16 (4 + n)

/--
The relocation for a RIP-relative displacement, chosen by what follows it.

`REL32` means "relative to the byte after the four-byte field". When the
instruction continues past that field -- an immediate, typically -- the target
is no longer computed from the right place, and COFF provides `REL32_1` through
`REL32_5` for one through five trailing bytes.

Measured, and the reason this is a function rather than a choice:
`mov DWORD PTR [rip+disp], imm32` gets `REL32_4`, `mov BYTE PTR [rip+disp],
imm8` gets `REL32_1`, and `mov WORD PTR [rip+disp], imm16` gets `REL32_2`. A
writer that reached for plain `REL32` on any of them would produce an address
wrong by exactly the number of trailing bytes -- a silent misresolution, not a
link error.

Six or more trailing bytes is refused rather than clamped: no encoding exists,
and there is no x86-64 instruction with a RIP-relative displacement followed by
more than an `imm32`. -/
def RelocationType.ripRelative? (trailing : Nat) : Option RelocationType :=
  if trailing = 0 then some .rel32
  else if trailing ≤ 5 then some (.rel32Trailing trailing)
  else none

/-- **A trailing count of five or fewer is accepted, and more is refused.** -/
theorem RelocationType.ripRelative?_isSome_iff (trailing : Nat) :
    (RelocationType.ripRelative? trailing).isSome ↔ trailing ≤ 5 := by
  unfold ripRelative?
  split <;> rename_i h
  · simp; omega
  · split <;> simp_all

/--
**The code of a RIP-relative relocation is four plus its trailing count.**

The whole content of the family, stated once. A model that picked the wrong
member of it produces an address off by the difference, and this is what makes
the choice checkable rather than a table to be trusted. -/
theorem RelocationType.ripRelative_code {trailing : Nat} {t : RelocationType}
    (h : RelocationType.ripRelative? trailing = some t) :
    t.code = BitVec.ofNat 16 (4 + trailing) := by
  unfold ripRelative? at h
  split at h <;> rename_i h0
  · simp only [Option.some.injEq] at h
    subst h
    simp [code, h0]
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · exact absurd h (by simp)

/--
**The three fixed kinds have distinct codes.**

Stated because the codes are adjacent small integers written by hand from the
specification, and a transposition between `addr32nb` and `rel32` produces an
object file that links and runs with every address computed against the wrong
base. The `REL32` family needs its own statement, below, because it is
parameterised. -/
theorem RelocationType.fixed_code_injective {a b : RelocationType}
    (ha : a = .addr64 ∨ a = .addr32nb ∨ a = .rel32)
    (hb : b = .addr64 ∨ b = .addr32nb ∨ b = .rel32)
    (h : a.code = b.code) : a = b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | rfl | (exfalso; exact absurd h (by decide))

/--
**Distinct trailing counts give distinct codes.**

Within the encodable range, which is what `ripRelative?` enforces. This is the
half of injectivity that matters for the `REL32` family: two relocations
differing only in how many bytes follow the displacement must not encode alike,
because the difference is exactly how far off the resolved address would be. -/
theorem RelocationType.rel32Trailing_code_injective {m n : Nat}
    (hm : m ≤ 5) (hn : n ≤ 5)
    (h : (RelocationType.rel32Trailing m).code
        = (RelocationType.rel32Trailing n).code) : m = n := by
  have ht := congrArg BitVec.toNat h
  simp only [code, BitVec.toNat_ofNat,
             Nat.mod_eq_of_lt (by omega : 4 + m < 65536),
             Nat.mod_eq_of_lt (by omega : 4 + n < 65536)] at ht
  omega

/--
**`rel32` and `rel32Trailing 0` encode alike, and `ripRelative?` picks the
first.**

The representation has a redundancy, and saying so is better than leaving a
reader to notice. Both encode to 4, so `RelocationType.code` is not injective
over the whole type -- only over the three fixed kinds, and separately over the
trailing counts, which is why those are two theorems rather than one.

A mutation making `ripRelative? 0` return the family member survived every
other check here, correctly: nothing observable distinguishes them. This pins
the canonical choice so that two values meaning the same thing do not both
circulate. -/
theorem RelocationType.rel32_zero_redundant :
    RelocationType.rel32.code = (RelocationType.rel32Trailing 0).code
    ∧ RelocationType.ripRelative? 0 = some .rel32 := by
  refine ⟨?_, ?_⟩ <;> decide
/-- One entry of a section's relocation directory: ten bytes. -/
structure Relocation where
  /-- Offset within the section's raw data of the field to fix up. -/
  virtualAddress : BitVec 32
  /-- Index of the symbol whose address is written there. -/
  symbolIndex : BitVec 32
  /-- How to compute the value. -/
  type : RelocationType
deriving DecidableEq, Repr, Inhabited

/--
The ten bytes, in file order.

The order is the whole content of this definition, and it is the thing a reader
recovers from an object file: `VirtualAddress`, then `SymbolTableIndex`, then a
two-byte `Type`. -/
def Relocation.toBytes (r : Relocation) : ByteSeq :=
  le32 r.virtualAddress ++ le32 r.symbolIndex ++ le16 r.type.code

/-- **A relocation is exactly ten bytes.**

The directory is an array with no separators, so a reader finds the *n*-th entry
by multiplying. A record of any other size silently reinterprets every entry
after the first. -/
@[simp] theorem Relocation.length_toBytes (r : Relocation) :
    r.toBytes.length = 10 := by
  simp [toBytes]

/-! ## Section headers -/

/--
A section name: at most eight bytes.

The field is eight bytes with no terminator, so a longer name is not truncated
by this model -- `SectionName.mk?` refuses it. A longer name in a real object
file is stored in the string table and referenced as `/`-plus-decimal, which
this profile does not emit and therefore does not model.
-/
structure SectionName where
  /-- The bytes, at most eight of them. -/
  bytes : ByteSeq
  /-- The bound the file format imposes. -/
  fits : bytes.length ≤ 8
deriving DecidableEq, Repr

/-- Build a name, or refuse one that cannot be stored. -/
def SectionName.mk? (bytes : ByteSeq) : Option SectionName :=
  if h : bytes.length ≤ 8 then some ⟨bytes, h⟩ else none

/-- **A refused name is one that does not fit.**

Both directions, so the refusal cannot be vacuous: everything within the bound
is accepted, and nothing beyond it is. -/
theorem SectionName.mk?_isSome_iff (bytes : ByteSeq) :
    (SectionName.mk? bytes).isSome ↔ bytes.length ≤ 8 := by
  unfold mk?; split <;> simp_all

/-- The eight-byte field: the name, zero-padded on the right. -/
def SectionName.toBytes (n : SectionName) : ByteSeq :=
  n.bytes ++ List.replicate (8 - n.bytes.length) 0

/-- **The name field is exactly eight bytes, whatever the name.**

The padding is what makes the section table a fixed stride, so this is the
theorem that keeps the table indexable. -/
@[simp] theorem SectionName.length_toBytes (n : SectionName) :
    n.toBytes.length = 8 := by
  have := n.fits
  simp [toBytes]
  omega

/--
One section header: forty bytes.

`pointerToRelocations` and `numberOfRelocations` are the two fields that make an
unlinked object file readable at all, per the header note above.
-/
structure SectionHeader where
  /-- The eight-byte name field. -/
  name : SectionName
  /-- Size in memory; zero in an object file. -/
  virtualSize : BitVec 32
  /-- Address in memory; zero in an object file. -/
  virtualAddress : BitVec 32
  /-- Size of the section's raw data in the file. -/
  sizeOfRawData : BitVec 32
  /-- File offset of the raw data. -/
  pointerToRawData : BitVec 32
  /-- File offset of the relocation directory. -/
  pointerToRelocations : BitVec 32
  /-- File offset of the line-number table; zero, which is what this profile
  emits and what modern toolchains expect. -/
  pointerToLinenumbers : BitVec 32
  /-- How many relocations follow `pointerToRelocations`. -/
  numberOfRelocations : BitVec 16
  /-- How many line numbers; zero here. -/
  numberOfLinenumbers : BitVec 16
  /-- Section flags. -/
  characteristics : BitVec 32
deriving DecidableEq, Repr

/-- The forty bytes, in file order. -/
def SectionHeader.toBytes (s : SectionHeader) : ByteSeq :=
  s.name.toBytes ++ le32 s.virtualSize ++ le32 s.virtualAddress ++
    le32 s.sizeOfRawData ++ le32 s.pointerToRawData ++
    le32 s.pointerToRelocations ++ le32 s.pointerToLinenumbers ++
    le16 s.numberOfRelocations ++ le16 s.numberOfLinenumbers ++
    le32 s.characteristics

/-- **A section header is exactly forty bytes.**

The section table immediately follows the file header with no padding, so a
reader locates section *n* by multiplying. This is the stride. -/
@[simp] theorem SectionHeader.length_toBytes (s : SectionHeader) :
    s.toBytes.length = 40 := by
  simp [toBytes]

/-! ## File header -/

/--
The COFF file header: twenty bytes.

`sizeOfOptionalHeader` is present and is zero for an object file. It is modelled
rather than omitted because a reader adds it to the header size to find the
section table, so a writer that dropped it would move every section header.
-/
structure FileHeader where
  /-- Target machine. -/
  machine : Machine
  /-- How many section headers follow. -/
  numberOfSections : BitVec 16
  /-- Creation stamp. -/
  timeDateStamp : BitVec 32
  /-- File offset of the symbol table. -/
  pointerToSymbolTable : BitVec 32
  /-- How many symbols it holds. -/
  numberOfSymbols : BitVec 32
  /-- Zero in an object file; nonzero only in an image. -/
  sizeOfOptionalHeader : BitVec 16
  /-- File flags. -/
  characteristics : BitVec 16
deriving DecidableEq, Repr

/-- The twenty bytes, in file order. -/
def FileHeader.toBytes (h : FileHeader) : ByteSeq :=
  le16 h.machine.code ++ le16 h.numberOfSections ++ le32 h.timeDateStamp ++
    le32 h.pointerToSymbolTable ++ le32 h.numberOfSymbols ++
    le16 h.sizeOfOptionalHeader ++ le16 h.characteristics

/-- **The file header is exactly twenty bytes.** -/
@[simp] theorem FileHeader.length_toBytes (h : FileHeader) :
    h.toBytes.length = 20 := by
  simp [toBytes]

/--
Where the section table starts, for a reader.

Twenty bytes of file header plus whatever the optional header claims. Written as
a definition rather than left to each caller because it is the one arithmetic
fact a reader needs before it can find anything at all, and getting it wrong
shifts every section by a constant -- which looks like a corrupt file rather
than like an off-by-one. -/
def FileHeader.sectionTableOffset (h : FileHeader) : Nat :=
  20 + h.sizeOfOptionalHeader.toNat

/-- **An object file's section table begins at byte twenty.**

The special case worth stating, since `sizeOfOptionalHeader` is zero for every
file this profile writes. -/
theorem FileHeader.sectionTableOffset_of_obj {h : FileHeader}
    (hz : h.sizeOfOptionalHeader = 0) : h.sectionTableOffset = 20 := by
  simp [sectionTableOffset, hz]

/-! ## Sections -/

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
-- Decidable equality so that cross-record predicates over a concrete object --
-- "this auxiliary record describes a section this file has" -- can be checked
-- by evaluation rather than by hand.
deriving DecidableEq

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

/-! ## A list lemma the layout proofs rest on -/

/--
Dropping a known-length prefix and `k` more leaves the rest dropped by `k`.

Generic, and here rather than beside its first user because both the section
layout and the string table need it: each reads at an offset measured past a
prefix whose length it knows. Keeping it in one place is also what lets those
two modules stay independent of each other. -/
theorem drop_length_append (a b : ByteSeq) (k : Nat) :
    (a ++ b).drop (a.length + k) = b.drop k := by
  induction a with
  | nil => simp
  | cons x rest ih =>
      simp only [List.length_cons, List.cons_append]
      rw [show rest.length + 1 + k = (rest.length + k) + 1 by omega,
          List.drop_succ_cons]
      exact ih

end Grass.Platform.Win32.Coff
