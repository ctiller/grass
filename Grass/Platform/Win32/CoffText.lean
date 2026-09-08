import Grass.Platform.Win32.CoffLayout

/-!
# Building `.text` as a COFF section

The last of the three section builders, and the only one whose relocations
point *into* instructions rather than into records.

`.pdata` and `.xdata` are tables: a relocation there addresses a field of a
twelve- or eighteen-byte record, and the record's shape says where. `.text` is
a byte stream whose structure only the encoder knows, so a displacement site
has to be given rather than derived -- which is exactly why it needs checking.

## The bound this enforces

A displacement field lives inside an instruction, and the instruction may
continue past it. So a site at offset `o` with `t` trailing bytes occupies
`o` through `o + 4 + t - 1`, and all of that must be inside the section.

An out-of-range site is not caught by anything else. The relocation record is
well formed, its type is a real type, and its offset is a plausible number; the
linker writes four bytes at that offset and, if the section is shorter, into
whatever follows it in the file. `DisplacementSite.InRange` is the condition,
and `textSection?` refuses a section any of whose sites fails it.

## Where a site's numbers come from

`DisplacementSite` is a bare triple, and an earlier version of this paragraph
said the trailing count was taken on trust because only an encoder knows how
long an instruction is. That was true and it is no longer necessary.
`Grass/ISA/X86/Bytes.lean` now exposes `dispOffset` and `dispTrailing`, and
`siteForInsn` builds the triple from an encoding, so neither number has to be
supplied by hand.

`DisplacementSite` stays a plain structure because a section may hold bytes
this profile did not encode -- a hand-written stub, or code from elsewhere --
and refusing those would be a stronger claim than this layer can make. The
derived path is the one to use where an encoding exists.

## What is still not modelled

That the symbol a site names is the one the instruction meant. `siteForInsn`
takes the symbol index as an argument, and nothing relates it to the operand
the encoder was given.
-/

namespace Grass.Platform.Win32.Coff

open Grass.Std.Logical (ByteSeq)

/--
One place in `.text` where the linker must write a displacement.

`trailing` is how many bytes of the instruction follow the four-byte field,
which is what picks the member of the `REL32` family.
-/
structure DisplacementSite where
  /-- Offset of the four-byte field within the section. -/
  fieldOffset : Nat
  /-- Symbol table record index the displacement resolves against. -/
  symbolIndex : BitVec 32
  /-- Instruction bytes following the field. -/
  trailing : Nat
deriving DecidableEq, Repr

/--
The site fits inside a section of `size` bytes.

Four bytes of field plus whatever follows it. Stated with the trailing bytes
included because a field that fits while its instruction does not is still a
section that ends mid-instruction. -/
abbrev DisplacementSite.InRange (d : DisplacementSite) (size : Nat) : Prop :=
  d.fieldOffset + 4 + d.trailing ≤ size

/-- The relocation, or nothing if the trailing count has no encoding. -/
def DisplacementSite.relocation? (d : DisplacementSite) : Option Relocation :=
  (RelocationType.ripRelative? d.trailing).map fun t =>
    ⟨BitVec.ofNat 32 d.fieldOffset, d.symbolIndex, t⟩

/-- **A site is encodable exactly when at most five bytes follow the field.** -/
theorem DisplacementSite.relocation?_isSome_iff (d : DisplacementSite) :
    d.relocation?.isSome ↔ d.trailing ≤ 5 := by
  unfold relocation?
  rw [Option.isSome_map]
  exact RelocationType.ripRelative?_isSome_iff d.trailing

/--
**An encodable site's relocation is a member of the `REL32` family.**

Not `ADDR32NB`, which is what `.pdata` and `.xdata` use. A displacement
resolved image-relative rather than PC-relative is wrong by the image base --
an address that looks plausible and is not. -/
theorem DisplacementSite.relocation_is_rel32 (d : DisplacementSite)
    {r : Relocation} (h : d.relocation? = some r) :
    r.type.code = BitVec.ofNat 16 (4 + d.trailing) := by
  unfold relocation? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨t, ht, hr⟩ := h
  subst hr
  exact RelocationType.ripRelative_code ht

/--
The site for a RIP-relative instruction placed at `base` in the section.

Both numbers come from the encoding: `dispOffset` says where the field sits
inside the instruction, and `dispTrailing` counts the immediate after it, which
is what picks the member of the `REL32` family. A caller supplies only where the
instruction was placed and which symbol it means.

`Grass.ISA.X86.InsnEncoding.dispOffset_add_disp_add_trailing` is what makes
this sound --
without it the two numbers could each be plausible and jointly describe a field
outside the instruction. -/
def siteForInsn (base : Nat) (i : Grass.ISA.X86.InsnEncoding)
    (symbolIndex : BitVec 32) : DisplacementSite where
  fieldOffset := base + i.dispOffset
  symbolIndex := symbolIndex
  trailing := i.dispTrailing

/--
**A derived site lies within the instruction that produced it.**

The field starts inside the instruction and the trailing bytes end exactly
where the instruction does, so a site derived this way is in range of any
section that contains the instruction. That is the property a hand-supplied
triple cannot be trusted to have. -/
theorem siteForInsn_within (base : Nat) (i : Grass.ISA.X86.InsnEncoding)
    (sym : BitVec 32) (hdisp : i.disp.size = 4) :
    (siteForInsn base i sym).InRange (base + i.size) := by
  simp only [siteForInsn, DisplacementSite.InRange]
  have h := Grass.ISA.X86.InsnEncoding.dispOffset_add_disp_add_trailing i
  rw [hdisp] at h
  omega

/-- Every site's relocation, or nothing if any is unencodable. -/
def displacementRelocations? (sites : List DisplacementSite) :
    Option (List Relocation) :=
  sites.foldr
    (fun d acc => match d.relocation?, acc with
      | some r, some rs => some (r :: rs)
      | _, _ => none)
    (some [])

/-- `.text`'s section flags: code, executable and readable. -/
def textCharacteristics : BitVec 32 := 0x60500020

/--
The section, or nothing if a site cannot be encoded or falls outside the code.

Both refusals matter and they are different. An unencodable site has no
relocation type; an out-of-range site has one that would make the linker write
past the section. -/
def textSection? (name : SectionName) (code : ByteSeq)
    (sites : List DisplacementSite) : Option Section :=
  if sites.all (fun d => decide (d.InRange code.length)) then
    (displacementRelocations? sites).map fun rs =>
      { name := name, data := code, relocations := rs
        characteristics := textCharacteristics }
  else none

/-- `.text`, for the theorems below, which need a closed term to evaluate. -/
def dotText : SectionName := ⟨[0x2e, 0x74, 0x65, 0x78, 0x74], by decide⟩

/--
**A site running past the end of the code is refused.**

The falsifying case, on a section of four bytes with a field at offset two: the
field alone needs six. Without this the range check could be stated and never
enforced. -/
theorem textSection?_refuses_out_of_range :
    textSection? dotText [0x90, 0x90, 0x90, 0x90] [⟨2, 0, 0⟩] = none := by
  decide

/-- **A site whose instruction fits is accepted.** -/
theorem textSection?_accepts_in_range :
    (textSection? dotText [0x90, 0x90, 0x90, 0x90, 0x90, 0x90] [⟨2, 0, 0⟩]).isSome
      := by decide

/--
**An unencodable trailing count is refused even when the site fits.**

The two refusals are independent, and a section long enough to hold a site says
nothing about whether the site has an encoding. -/
theorem textSection?_refuses_unencodable :
    textSection? dotText (List.replicate 32 0x90) [⟨2, 0, 6⟩] = none := by
  decide

end Grass.Platform.Win32.Coff
