import Grass.Platform.Win32.CoffPdata

/-!
# Building `.xdata`, and pointing `.pdata` at it

`.pdata` says where each function's unwind data *is*; `.xdata` is where it
actually sits. `CoffPdata.lean` takes `unwindOffset` on trust -- a number a
caller supplies -- and this is what makes that number true.

## The two sections have to agree, and nothing so far made them

`PdataEntry.unwindOffset` is the addend on `UnwindInfoAddress`, so the linker
computes `.xdata`'s address plus that offset. If the offset is not where the
block was laid out, the unwinder reads another function's prologue and
"succeeds": it decodes a valid `UNWIND_INFO` describing the wrong frame, which
is worse than failing, because the stack walk continues with a corrupt frame
pointer rather than stopping.

`entries_point_at_blocks` is the statement that they agree. This is the fourth
time in these modules that a definition assigning offsets and a theorem reading
at them needed something to connect them, and the first time the two are in
different sections.

## Alignment

Two boundaries matter and they are different. The section is placed on an
eight-byte boundary -- see `xdataCharacteristics` -- while each `UNWIND_INFO`
inside it must begin on a four-byte one. This module handles the second;
the first is a fact about the section header.

`UNWIND_INFO` must begin on a four-byte boundary. Blocks this profile produces
are already a multiple of four -- a four-byte header plus two bytes per slot
with slots padded to an even count -- so in practice no padding is emitted, and
the measured object confirms it: two eight-byte blocks at offsets zero and
eight.

`xdataBytes` pads anyway, because this module takes opaque byte sequences rather
than `Grass.ABI.Win64.UnwindInfo` values, and an unaligned block supplied by a
future caller would otherwise misalign every block after it.
-/

namespace Grass.Platform.Win32.Coff

open Grass.Std.Logical (ByteSeq)

/-- Bytes of padding needed to reach the next four-byte boundary. -/
def alignPad (n : Nat) : Nat := (4 - n % 4) % 4

/-- **Padding brings a length up to a multiple of four.** -/
theorem alignPad_aligns (n : Nat) : (n + alignPad n) % 4 = 0 := by
  unfold alignPad
  omega

/-- **A length already aligned needs no padding.**

Stated because the sizes this profile produces are all multiples of four, so
this is the case that actually occurs; without it the padding could be wrong in
exactly the situation that never gets tested. -/
theorem alignPad_of_aligned {n : Nat} (h : n % 4 = 0) : alignPad n = 0 := by
  unfold alignPad
  omega

/-- One block, padded to a four-byte boundary. -/
def xdataBlock (b : ByteSeq) : ByteSeq :=
  b ++ List.replicate (alignPad b.length) 0

/-- **A padded block's length is a multiple of four.** -/
theorem length_xdataBlock_aligned (b : ByteSeq) :
    (xdataBlock b).length % 4 = 0 := by
  simp only [xdataBlock, List.length_append, List.length_replicate]
  exact alignPad_aligns b.length

/-- **A block that was already aligned is unchanged.** -/
theorem xdataBlock_of_aligned {b : ByteSeq} (h : b.length % 4 = 0) :
    xdataBlock b = b := by
  simp [xdataBlock, alignPad_of_aligned h]

/-- The section's contents: every block, each padded. -/
def xdataBytes (blocks : List ByteSeq) : ByteSeq :=
  (blocks.map xdataBlock).flatten

/-- Where each block starts. -/
def xdataOffsets (start : Nat) : List ByteSeq → List Nat
  | [] => []
  | b :: rest => start :: xdataOffsets (start + (xdataBlock b).length) rest

/-- **Block offsets split at a concatenation.** -/
theorem xdataOffsets_append (start : Nat) (pre post : List ByteSeq) :
    xdataOffsets start (pre ++ post)
      = xdataOffsets start pre
        ++ xdataOffsets (start + (xdataBytes pre).length) post := by
  induction pre generalizing start with
  | nil => simp [xdataOffsets, xdataBytes]
  | cons x rest ih =>
      simp only [List.cons_append, xdataOffsets, ih, xdataBytes,
                 List.map_cons, List.flatten_cons, List.length_append]
      rw [show start + (xdataBlock x).length
            + ((rest.map xdataBlock).flatten).length
            = start + ((xdataBlock x).length
                + ((rest.map xdataBlock).flatten).length) by omega]

/--
**Reading at a block's offset returns that block, padding and all.**

The `.xdata` counterpart of `data_at_layout_offset`, and the fact
`entries_point_at_blocks` rests on. -/
theorem block_at_offset (pre : List ByteSeq) (b : ByteSeq)
    (post : List ByteSeq) :
    ((xdataBytes (pre ++ b :: post)).drop (xdataBytes pre).length).take
        (xdataBlock b).length
      = xdataBlock b := by
  have hsplit : xdataBytes (pre ++ b :: post)
      = xdataBytes pre ++ (xdataBlock b ++ xdataBytes post) := by
    simp [xdataBytes]
  rw [hsplit, List.drop_left, List.take_left]

/--
`.xdata`'s section flags: initialised read-only data, **eight**-byte aligned.

An earlier version of this had `0x40300040`, copied from `.pdata`. The two
differ, and in the field that matters here: `0x300000` is `ALIGN_4BYTES` and
`0x400000` is `ALIGN_8BYTES`, so `.pdata` is four-byte aligned and `.xdata` is
eight. `ml64` writes `0x40400040`.

Two alignments are in play and they are not the same one. The *section* is
placed on an eight-byte boundary, which this constant states; each
`UNWIND_INFO` *within* it must begin on a four-byte boundary, which `alignPad`
handles. Copying `.pdata`'s word made the first wrong while leaving the second
right, which is why the mistake survived the block-offset theorems. -/
def xdataCharacteristics : BitVec 32 := 0x40400040

/--
The whole section.

Relocations are a parameter and not `[]`, which an earlier version of this had.
Unwind data with no handler refers to nothing outside itself -- the measured
two-function object has zero `.xdata` relocations -- and hardcoding that made
the common case true and the interesting one inexpressible. A handler-bearing
`UNWIND_INFO` carries one `ADDR32NB` for its handler field, at the block's
offset plus four plus twice the padded slot count; the first object measured for
these modules had exactly that, pointing at `grasshandler`.

The caller supplies them because this module does not decode blocks: it takes
opaque bytes, so it cannot know where inside one a handler field sits. An
emitter that built the block knows. -/
def xdataSection (name : SectionName) (blocks : List ByteSeq)
    (relocations : List Relocation) : Section where
  name := name
  data := xdataBytes blocks
  relocations := relocations
  characteristics := xdataCharacteristics

/--
**Unwind data with no handler needs no relocations.**

The case the measured object shows, stated so that passing `[]` is a choice
recorded here rather than a property of the builder. -/
theorem xdataSection_handlerless (name : SectionName) (blocks : List ByteSeq) :
    (xdataSection name blocks []).relocations = [] := rfl

/--
**A `.pdata` entry whose `unwindOffset` is a block's offset reads that block.**

The cross-section statement. Given the offset `xdataOffsets` assigned to a
block, an entry carrying that offset as its `UnwindInfoAddress` addend points at
exactly those bytes.

The bound is the field's width: `unwindOffset` is thirty-two bits, so an
`.xdata` section larger than four gigabytes could not address its own later
blocks. -/
theorem entries_point_at_blocks (pre : List ByteSeq) (b : ByteSeq)
    (post : List ByteSeq) (e : PdataEntry)
    (hoff : (xdataBytes pre).length < 2 ^ 32)
    (he : e.unwindOffset = BitVec.ofNat 32 (xdataBytes pre).length) :
    ((xdataBytes (pre ++ b :: post)).drop e.unwindOffset.toNat).take
        (xdataBlock b).length
      = xdataBlock b := by
  rw [he]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
  exact block_at_offset pre b post

end Grass.Platform.Win32.Coff
