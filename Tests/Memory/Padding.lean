import Grass.Memory.Shape

/-!
# Padding, on a struct that actually has some

`Grass/Memory/Shape.lean` proves that writing an aggregate's fields leaves its
padding exactly as it was. A theorem about padding is only worth as much as the
existence of a footprint with padding in it, so this file builds one and runs the
writes.

The struct is the smallest one that pads for a real reason: a one-byte field
followed by a four-byte field whose alignment forces it to offset four, in an
aggregate whose size is a multiple of its alignment. Offsets one, two, and three
are padding, and no field write touches them.

```text
offset  0  1  2  3  4  5  6  7
field   a  .  .  .  b  b  b  b
```

`docs/ASSEMBLY_CONSTRUCTION.md` §3's `StructLayout` is what would derive this
layout from field types and an ABI profile. Nothing here derives it: the
footprint is written out, because the memory layer's claim is about what follows
from a footprint and not about how one is computed.
-/

namespace Tests.Memory.Padding

open Grass.Core Grass.Memory Grass.Std.Logical

/-- The one-byte field at offset zero. -/
def fieldA : FieldFootprint := ⟨⟨"a"⟩, ⟨0, 1⟩⟩

/-- The four-byte field at offset four, where its alignment puts it. -/
def fieldB : FieldFootprint := ⟨⟨"b"⟩, ⟨4, 4⟩⟩

/-- The aggregate: two fields, eight bytes, three of them padding. -/
def layout : Footprint := ⟨[fieldA, fieldB], ⟨0, 8⟩⟩

/-- The footprint is well formed, so the framing theorems apply to it. -/
theorem layout_wellFormed : layout.WellFormed where
  namesUnique := by decide
  fieldsDisjoint := by decide
  fieldsContained := by decide

/-- Offsets one, two, and three are padding, and offsets zero and four are not.
Without this the padding theorems below would be vacuous. -/
theorem padding_is_where_expected :
    layout.IsPadding 1 ∧ layout.IsPadding 2 ∧ layout.IsPadding 3 ∧
    ¬ layout.IsPadding 0 ∧ ¬ layout.IsPadding 4 := by decide

/-- The allocation the fixture works in, and its epoch. Minted from the
supplies rather than written as literals, because `Uid.mk` is private. -/
def alloc : AllocId := (FreshSupply.initial (Tag := AllocTag)).fresh.1

/-- This allocation's reuse generation. -/
def epoch : EpochId := (FreshSupply.initial (Tag := EpochTag)).fresh.1

/-- An eight-byte allocation holding nothing. Every byte starts uninitialized,
which is the state a fresh allocation is actually in — `docs/MEMORY_MODEL.md` §4
does not hand out zeros. -/
def state₀ : MemoryState :=
  MemoryState.empty.allocate alloc
    { extent := ⟨0, 8⟩, epoch := epoch, space := .cpuVirtual
      permission := .readWrite, live := true, bytes := .empty }

/-- Writing both fields, with data of exactly each field's width. -/
def writes : List (FieldFootprint × ByteSeq) :=
  [(fieldA, [0xAA]), (fieldB, [0xBB, 0xBB, 0xBB, 0xBB])]

/-- Both fields written, in declaration order. -/
def state₁ : MemoryState := state₀.writeFields alloc 0 writes

/-- Every write in the schedule names a field of this footprint, which is the
hypothesis the padding theorem takes. -/
theorem writes_are_fields : ∀ write ∈ writes, write.1 ∈ layout.fields := by decide

/--
**The struct is not fully initialized after every field is written.**

The consequence that matters, and the one a typed shape could otherwise hide: an
access over the whole aggregate demanding `.allBytesInitialized` is still refused,
because three of its eight bytes were never written by anything.
-/
theorem the_aggregate_is_not_fully_initialized :
    ¬ state₁.RangeInitialized alloc ⟨0, 8⟩ := by decide

/-- Each padding byte in particular. -/
theorem padding_bytes_are_uninitialized :
    ¬ state₁.InitializedAt alloc 1 ∧ ¬ state₁.InitializedAt alloc 2 ∧
    ¬ state₁.InitializedAt alloc 3 := by decide

/-- The field bytes, by contrast, are initialized — so the theorem above is about
padding rather than about nothing having been written. -/
theorem field_bytes_are_initialized :
    state₁.RangeInitialized alloc fieldA.range ∧
    state₁.RangeInitialized alloc fieldB.range := by decide

/-- And they read back what was written. -/
theorem fields_read_back :
    state₁.byteAt? alloc 0 = some 0xAA ∧ state₁.byteAt? alloc 4 = some 0xBB ∧
    state₁.byteAt? alloc 7 = some 0xBB := by decide

/-- Padding holds no byte at all, not merely an uninitialized one. A store that
had quietly zero-filled the gap would fail here even if it had somehow kept the
initialization flags right. -/
theorem padding_holds_no_bytes :
    state₁.byteAt? alloc 1 = Option.none ∧ state₁.byteAt? alloc 2 = Option.none ∧
    state₁.byteAt? alloc 3 = Option.none := by decide

/--
The general theorem, instantiated here.

`padding_uninitialized_after_writing_fields` is proved for any schedule of the
aggregate's fields; the fixtures above run one. This checks the two agree, so a
change that broke the general proof could not be hidden by a fixture that happened
to still pass.
-/
theorem general_theorem_applies :
    ¬ state₁.InitializedAt alloc 2 :=
  MemoryState.padding_uninitialized_after_writing_fields (f := layout) state₀ alloc 0
    (offset := 2) (by decide) writes writes_are_fields (by decide)

end Tests.Memory.Padding
