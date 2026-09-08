import Grass.Platform.Win32.CoffLayout

/-!
# Building `.pdata` as a COFF section

The seam between the two trees this agent owns: `Grass/ABI/Win64/**` says what
an unwind table means, `Grass/Platform/Win32/**` says what an object file looks
like, and a `.pdata` section is the second holding the first.

## Why the entries are almost entirely zero

A `RUNTIME_FUNCTION` is three image-relative addresses, and in an object file
none of them is known -- the linker assigns them. So the twelve bytes an entry
occupies are zero except for the one field that *is* known before layout: the
function's length, which sits in `EndAddress` as the addend of its relocation.
The measured object shows exactly that: `00 00 00 00 07 00 00 00 00 00 00 00`
for a seven-byte function.

The other two fields hold addends rather than addresses: `EndAddress` carries
the function's length and `UnwindInfoAddress` carries the offset of that
function's unwind data inside the shared `.xdata` section. Everything else about
the entry -- which symbol each field resolves against -- lives in the relocation
directory, which is why `PdataEntry.relocations` carries the structure and the
bytes carry almost none of it.

## What the direction of this dependency is, and why

`Grass/Platform/Win32` imports nothing from `Grass/ABI/Win64` here, and that is
deliberate rather than accidental. This module takes a symbol index, an unwind
symbol index and a length -- three numbers -- rather than a
`Grass.ABI.Win64.RuntimeFunction`. The ABI layer's record is about *addresses
after linking*, which is a different thing from what a writer has before it, and
coupling the two would make the file format depend on a representation it cannot
fill in. When an emitter has both, it converts; neither layer needs the other.

## Not modelled

Ordering and separation across entries. `Grass/ABI/Win64/UnwindBytes.lean`'s
`PdataSection.Separated` and the ascending order its `WellFormed` requires are
properties of the *linked* addresses, and nothing here can establish them: every
`BeginAddress` in this section is zero until a linker runs. Those remain owed by
that module, and this one does not pretend to discharge them.
-/

namespace Grass.Platform.Win32.Coff

open Grass.ISA.X86 (le32)
open Grass.Std.Logical (ByteSeq)

/--
One `.pdata` entry as a writer knows it, before linking.

Three numbers, not three addresses: the symbol standing for the function, the
symbol standing for its `UNWIND_INFO`, and the function's length in bytes.
-/
structure PdataEntry where
  /-- Symbol table index of the function. -/
  functionSymbol : BitVec 32
  /-- Symbol table index of the section holding this function's
  `UNWIND_INFO` -- typically one `$xdatasym` shared by every function in the
  object, not one symbol per function. -/
  unwindSymbol : BitVec 32
  /-- The function's length, which becomes `EndAddress`'s addend. -/
  functionLength : BitVec 32
  /-- Where this function's `UNWIND_INFO` sits inside the section
  `unwindSymbol` names, which becomes `UnwindInfoAddress`'s addend. -/
  unwindOffset : BitVec 32
deriving DecidableEq, Repr

/--
The twelve bytes: a zero, the length, and the unwind offset.

`BeginAddress` is zero because its relocation supplies the whole address. The
other two hold addends the linker adds to a resolved symbol: `EndAddress` gets
the function's length, and `UnwindInfoAddress` gets the offset of this
function's `UNWIND_INFO` within the shared `.xdata` section.

That third field was written as zero in an earlier version of this module, and
it was wrong. A one-function object cannot show it -- the only `UNWIND_INFO` is
at offset zero -- so a fixture with a single entry passed. Measuring an object
with two functions gave `00 00 00 00 07 00 00 00 08 00 00 00` for the second,
where the trailing eight is exactly the byte offset of that function's unwind
data. A model that hardcoded zero would point every function after the first at
the first one's prologue. -/
def PdataEntry.toBytes (e : PdataEntry) : ByteSeq :=
  le32 0 ++ le32 e.functionLength ++ le32 e.unwindOffset

/-- **An entry is exactly twelve bytes.** -/
@[simp] theorem PdataEntry.length_toBytes (e : PdataEntry) :
    e.toBytes.length = 12 := by simp [toBytes]

/--
The three relocations for the entry at index `i`.

Offsets `12 * i`, `12 * i + 4` and `12 * i + 8`: the three fields of the `i`-th
`RUNTIME_FUNCTION`. `BeginAddress` and `EndAddress` name the *same* symbol,
which is what makes the entry a range over one function; only
`UnwindInfoAddress` names a different one. -/
def PdataEntry.relocations (e : PdataEntry) (i : Nat) : List Relocation :=
  [ ⟨BitVec.ofNat 32 (12 * i), e.functionSymbol, .addr32nb⟩
  , ⟨BitVec.ofNat 32 (12 * i + 4), e.functionSymbol, .addr32nb⟩
  , ⟨BitVec.ofNat 32 (12 * i + 8), e.unwindSymbol, .addr32nb⟩ ]

/-- **An entry contributes exactly three relocations.** -/
@[simp] theorem PdataEntry.length_relocations (e : PdataEntry) (i : Nat) :
    (e.relocations i).length = 3 := rfl

/--
**Every `.pdata` relocation is image-relative.**

`ADDR32NB` and not `ADDR32`: an absolute thirty-two bit address would be a
different fix-up entirely, and one that cannot represent a loaded image above
four gigabytes. The three entries are written by hand, so this is worth
stating. -/
theorem PdataEntry.relocations_all_addr32nb (e : PdataEntry) (i : Nat) :
    ∀ r ∈ e.relocations i, r.type = .addr32nb := by
  intro r hr
  simp [relocations] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

/--
**The two address fields of an entry name the same symbol.**

An entry describes one function, so `BeginAddress` and `EndAddress` must
resolve against the same symbol and differ only by the addend. Naming two
symbols would produce a range spanning whatever the linker happened to lay out
between them. -/
theorem PdataEntry.begin_end_same_symbol (e : PdataEntry) (i : Nat) :
    ∃ begin_ end_ unwind,
      e.relocations i = [begin_, end_, unwind]
      ∧ begin_.symbolIndex = end_.symbolIndex
      ∧ begin_.symbolIndex = e.functionSymbol
      ∧ unwind.symbolIndex = e.unwindSymbol :=
  ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- All entries' bytes, in order. -/
def pdataBytes (entries : List PdataEntry) : ByteSeq :=
  (entries.map PdataEntry.toBytes).flatten

/-- **The section's data is twelve bytes per entry.** -/
@[simp] theorem length_pdataBytes (entries : List PdataEntry) :
    (pdataBytes entries).length = 12 * entries.length := by
  induction entries with
  | nil => rfl
  | cons e rest ih => simp [pdataBytes] at *; omega

/-- Every entry's relocations, each numbered by its position. -/
def pdataRelocations (entries : List PdataEntry) : List Relocation :=
  (entries.zipIdx.map (fun p => p.1.relocations p.2)).flatten

/-- **Three relocations per pair, whatever indices the pairs carry.**

Stated over an arbitrary list of (entry, index) pairs rather than over
`zipIdx`'s output, because the induction has to generalise: `zipIdx` on a cons
numbers the tail from one, so an induction hypothesis about a tail numbered from
zero does not apply. The count does not depend on the indices at all, which is
what makes the general statement the easy one. -/
theorem length_flatten_entry_relocations (l : List (PdataEntry × Nat)) :
    ((l.map (fun p => p.1.relocations p.2)).flatten).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons p rest ih => simp [ih]; omega

/-- **There are three relocations per entry.** -/
@[simp] theorem length_pdataRelocations (entries : List PdataEntry) :
    (pdataRelocations entries).length = 3 * entries.length := by
  rw [pdataRelocations, length_flatten_entry_relocations, List.length_zipIdx]

/-- `.pdata`'s section flags: initialised read-only data. -/
def pdataCharacteristics : BitVec 32 := 0x40300040

/--
The whole section.

Name, bytes and relocations together, so a caller cannot supply a `.pdata`
whose relocations do not match its entries. -/
def pdataSection (name : SectionName) (entries : List PdataEntry) : Section where
  name := name
  data := pdataBytes entries
  relocations := pdataRelocations entries
  characteristics := pdataCharacteristics

end Grass.Platform.Win32.Coff
