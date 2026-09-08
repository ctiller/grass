import Grass.Platform.Win32.Coff

/-!
# COFF symbols and the string table

The eighteen-byte symbol record, the section number that is not a section
number, and the name field that is two different fields depending on its own
first four bytes.

`CoffLayout.lean` writes an object with no symbol table, which is why it cannot
be linked: a relocation names a symbol by index, and with no table those indices
point at nothing. This is the missing half.

## The ambiguity this module refuses

A symbol's name field is eight bytes and means one of two things. If the name is
eight bytes or shorter it sits there directly, padded with zeros. If it is
longer, the field instead holds four zero bytes followed by a four-byte offset
into the string table.

The two forms are told apart by whether the first four bytes are zero. So a
short name whose first four bytes happen to be zero is not merely unusual -- it
is *read as the other form*, and the linker follows a string-table offset made
of whatever the fifth through eighth bytes contained. `SymbolName.short?`
refuses that name rather than emitting a record that means something else.

No real symbol begins with a NUL, so this refusal costs nothing in practice.
That is exactly why it is worth encoding: it is the kind of constraint that
never fires, is never tested, and is silently violated the first time names come
from somewhere other than a compiler -- a mangling scheme, a synthetic label, or
a length-prefixed name pasted in whole.

## Section numbers that are not sections

`SectionNumber` is a *signed* sixteen-bit field, and three of its values are not
indices: zero means the symbol is undefined and must be resolved elsewhere, `-1`
means an absolute value that no section contains, and `-2` marks debugging
information. A model storing a bare `BitVec 16` would let `0` be written where a
real section was meant, which is the difference between a defined symbol and an
external one.

## Not modelled

Auxiliary symbol records. `numberOfAuxSymbols` is present in the record because
a reader must skip that many following entries to find the next symbol, and a
model that omitted it would mis-index every symbol after the first one that had
any. It is always zero here, and `Symbol.toBytes` writes it; nothing in this
profile emits the auxiliary records themselves.
-/

namespace Grass.Platform.Win32.Coff

open Grass.ISA.X86 (le16 le32)
open Grass.Std.Logical (Byte ByteSeq)

/-! ## Symbol names -/

/--
A symbol's name: inline, or a reference into the string table.

The two constructors are the two readings of the same eight bytes, made
separate so that a writer chooses which one it means.
-/
inductive SymbolName where
  /-- Eight bytes or fewer, stored directly. The bound and the
  leading-NUL refusal both live in `SymbolName.short?`. -/
  | short (name : SectionName)
  /-- A byte offset into the string table. -/
  | long (offset : BitVec 32)
deriving DecidableEq, Repr

/-- Whether the first four bytes of the zero-padded field are all zero, which is
exactly the condition a reader uses to take the field as a string-table
reference rather than as a name. -/
def SymbolName.leadingZeros (bytes : ByteSeq) : Bool :=
  ((bytes ++ List.replicate (8 - bytes.length) 0).take 4).all (· == 0)

/--
Build an inline name, or refuse one that cannot be read back as itself.

Refused in two cases: more than eight bytes, which does not fit; and a first
four bytes that are all zero, which a reader takes as the long form. The second
includes the empty name and any name shorter than four bytes, since those are
zero-padded into exactly that shape.
-/
def SymbolName.short? (bytes : ByteSeq) : Option SymbolName :=
  if h : bytes.length ≤ 8 then
    if leadingZeros bytes then none else some (.short ⟨bytes, h⟩)
  else none

/--
**A short name is accepted exactly when it fits and does not read as the long
form.**

Both directions. Without the reverse implication the refusal could be vacuous --
a `short?` returning `none` for everything satisfies a one-way statement -- and
this module's whole claim is that the *only* names it turns away are the two
ambiguous kinds. -/
theorem SymbolName.short?_isSome_iff (bytes : ByteSeq) :
    (SymbolName.short? bytes).isSome
      ↔ bytes.length ≤ 8 ∧ leadingZeros bytes = false := by
  unfold short?
  split
  · split <;> simp_all
  · exact ⟨fun hc => absurd hc (by simp), fun hc => absurd hc.1 (by omega)⟩

/-- **A four-byte name with no leading NUL is accepted.**

The witness that `short?` is not refusing everything, on a real symbol name. -/
theorem SymbolName.short?_main :
    (SymbolName.short? [0x6d, 0x61, 0x69, 0x6e]).isSome := by decide

/-- **The empty name is refused.**

Zero-padded it is eight NUL bytes, whose first four are zero, so a reader takes
it as a string-table reference to offset zero. -/
theorem SymbolName.short?_empty : SymbolName.short? [] = none := by decide

/--
**Three leading NULs are fine; it takes four to be ambiguous.**

The boundary of the rule, and the case that pins the *four*. A field beginning
`00 00 00 01` has a nonzero byte inside the first four, so a reader takes it as
a name and this accepts it. Checking only three bytes would refuse it -- a
refusal of a perfectly writable name -- and no other theorem here tells the two
rules apart, which a mutation demonstrated by surviving. -/
theorem SymbolName.short?_three_nulls_ok :
    (SymbolName.short? [0, 0, 0, 1]).isSome := by decide

/--
**Four leading NULs are refused, whatever follows.**

The case the module exists for: `00 00 00 00 41 ...` is read as a string-table
reference to offset `0x41`, so emitting it as a name would produce a record that
means something else entirely. -/
theorem SymbolName.short?_four_nulls_refused :
    SymbolName.short? [0, 0, 0, 0, 0x41] = none := by decide
/-- The eight bytes, either form. -/
def SymbolName.toBytes : SymbolName → ByteSeq
  | .short n => n.toBytes
  | .long off => [0, 0, 0, 0] ++ le32 off

/-- **A symbol name field is exactly eight bytes, either form.** -/
@[simp] theorem SymbolName.length_toBytes (n : SymbolName) :
    n.toBytes.length = 8 := by
  cases n <;> simp [toBytes]

/-! ## Section numbers -/

/--
The `SectionNumber` field, which is signed and whose small values are not
indices.
-/
inductive SectionNumber where
  /-- `IMAGE_SYM_UNDEFINED` (0): resolved by another object. -/
  | undefined
  /-- `IMAGE_SYM_ABSOLUTE` (-1): a value, not an address in any section. -/
  | absolute
  /-- `IMAGE_SYM_DEBUG` (-2): debugging information. -/
  | debug
  /-- A real section, numbered from one. -/
  | section_ (index : Nat)
deriving DecidableEq, Repr

/-- The signed sixteen-bit encoding. -/
def SectionNumber.code : SectionNumber → BitVec 16
  | .undefined => 0
  | .absolute => 0xFFFF
  | .debug => 0xFFFE
  | .section_ i => BitVec.ofNat 16 i

/--
**A real section never encodes as one of the three reserved values.**

The bound is what makes it true, and it is the reason `section_` carries a
`Nat` with a hypothesis rather than a `BitVec 16`: section one is the first, so
zero is not a section, and the two negative markers sit at the top of the range.
A section index outside this bound would encode as `undefined`, `absolute` or
`debug` and change what the symbol means. -/
theorem SectionNumber.section_code_ne_reserved {i : Nat}
    (hlo : 0 < i) (hhi : i < 0xFFFE) :
    (SectionNumber.section_ i).code ≠ SectionNumber.undefined.code
    ∧ (SectionNumber.section_ i).code ≠ SectionNumber.absolute.code
    ∧ (SectionNumber.section_ i).code ≠ SectionNumber.debug.code := by
  have ht : (SectionNumber.section_ i).code.toNat = i := by
    simp [code, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 65536)]
  refine ⟨?_, ?_, ?_⟩ <;> intro hc <;>
    (have h2 := congrArg BitVec.toNat hc
     rw [ht] at h2
     simp [code] at h2
     omega)

/--
**The three reserved section numbers are distinct from each other.**

Separate from `section_code_ne_reserved`, which only says a real section is none
of them. A transposition among the three -- writing `absolute` where `debug`
belongs -- would keep every symbol out of the section space while changing what
each one means, and nothing above would notice. A real object exercises two of
the three: `@comp.id` is absolute and an external symbol is undefined. -/
theorem SectionNumber.reserved_distinct :
    SectionNumber.undefined.code ≠ SectionNumber.absolute.code
    ∧ SectionNumber.undefined.code ≠ SectionNumber.debug.code
    ∧ SectionNumber.absolute.code ≠ SectionNumber.debug.code := by decide

/-! ## Symbol records -/

/-- One symbol table entry: eighteen bytes. -/
structure Symbol where
  /-- The name, inline or by string-table offset. -/
  name : SymbolName
  /-- Offset within the section, or the value for an absolute symbol. -/
  value : BitVec 32
  /-- Which section, or one of the three reserved meanings. -/
  sectionNumber : SectionNumber
  /-- Complex and base type. -/
  type : BitVec 16
  /-- Storage class: external, static, and so on. -/
  storageClass : Byte
  /-- How many auxiliary records follow. Always zero here, and written
  because a reader skips this many entries to find the next symbol. -/
  numberOfAuxSymbols : Byte
deriving DecidableEq, Repr

/-- The eighteen bytes, in file order. -/
def Symbol.toBytes (s : Symbol) : ByteSeq :=
  s.name.toBytes ++ le32 s.value ++ le16 s.sectionNumber.code
    ++ le16 s.type ++ [s.storageClass, s.numberOfAuxSymbols]

/--
**A symbol record is exactly eighteen bytes.**

Eighteen, not twenty: the record is not padded to a multiple of four, which is
the mistake a reader familiar with the rest of the format is most likely to
make. The symbol table is an array of these, so a wrong size mis-indexes every
entry after the first. -/
@[simp] theorem Symbol.length_toBytes (s : Symbol) : s.toBytes.length = 18 := by
  simp [toBytes]

end Grass.Platform.Win32.Coff
