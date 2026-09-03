import Grass.Std.Logical.Vec

/-!
# Chunk boundaries are not observable

`docs/STDLIB.md` §6 gives `Std.Process.ByteFlow` a contract whose sequence half
is a claim about what a parser can see:

> Positive partial reads produce nonempty ordered chunks; parsers consume their
> concatenation independent of chunk boundaries.

`Grass/Std/Logical/Vec.lean` proves `Vec.chunk_extensional`, which is that claim
for any consumer at all. This fixture is the part a theorem cannot carry: that
the statement is about something, by exhibiting two genuinely different chunkings
of the same bytes and a consumer that cannot tell them apart.

The read side and the write side now meet. `Tests/Std/PartialWrite.lean` shows a
writer committing exact prefixes of a payload; this shows a reader receiving that
payload in arbitrary pieces. Both reduce to `Vec` laws and neither mentions a
handle.
-/

namespace Grass.Tests.Std.Chunking

open Grass.Std.Logical

/-! ## Two chunkings of the same bytes

`"Hi!"` arriving whole, in three single-byte reads, and split unevenly. A
provider is entitled to any of these and a parser must not care which it got.
-/

def message : Vec Byte := Vec.fromList [0x48, 0x69, 0x21]

def whole : Vec (Vec Byte) := Vec.singleton message

def byteAtATime : Vec (Vec Byte) :=
  Vec.fromList [Vec.fromList [0x48], Vec.fromList [0x69], Vec.fromList [0x21]]

def uneven : Vec (Vec Byte) :=
  Vec.fromList [Vec.fromList [0x48, 0x69], Vec.fromList [0x21]]

example : Vec.IsChunking whole message := Vec.isChunking_singleton message
example : Vec.IsChunking byteAtATime message := rfl
example : Vec.IsChunking uneven message := rfl

/-- The chunkings really are different values, so the theorem below is not
vacuous. -/
example : byteAtATime ≠ uneven := by
  intro h
  have := congrArg Vec.length h
  simp [byteAtATime, uneven] at this

/-! ## A consumer of the concatenation cannot distinguish them -/

/-- A stand-in parser: it reads the whole input and reports a length and a first
byte. Anything expressible as a function of the concatenation will do. -/
def parse (input : Vec Byte) : Nat × Option Byte := (input.length, input.get? 0)

example :
    parse (Vec.flatten byteAtATime) = parse (Vec.flatten uneven) :=
  Vec.chunk_extensional parse (rfl : Vec.IsChunking byteAtATime message) rfl

example :
    parse (Vec.flatten whole) = parse (Vec.flatten byteAtATime) :=
  Vec.chunk_extensional parse (Vec.isChunking_singleton message) rfl

/-- Concretely, all three give the same answer. -/
example : parse (Vec.flatten byteAtATime) = (3, some 0x48) := rfl
example : parse (Vec.flatten uneven) = (3, some 0x48) := rfl
example : parse (Vec.flatten whole) = (3, some 0x48) := rfl

/-! ## Accumulating chunks

A reader appends chunks as they arrive. `Vec.flatten_push` is the step law: one
more chunk extends the accumulated bytes by exactly that chunk.
-/

example :
    Vec.flatten (Vec.empty.push (Vec.fromList [0x48, 0x69]) |>.push (Vec.fromList [0x21]))
      = message := rfl

example (chunks : Vec (Vec Byte)) (chunk : Vec Byte) :
    Vec.flatten (chunks.push chunk) = Vec.flatten chunks ++ chunk :=
  Vec.flatten_push chunks chunk

/-! ## Why the chunks have to be nonempty

`docs/STDLIB.md` §6 says *positive* partial reads. Without that word a provider
could return unboundedly many empty chunks while a reader waited for input that
never arrived, and no length argument would notice. `Vec.length_le_length_flatten`
is what rules it out, and it is the read-side counterpart of
`Vec.length_drop_lt_of_pos` in the write-side fixture.
-/

theorem byteAtATime_nonEmpty : Vec.AllNonEmpty byteAtATime := by
  intro chunk hmem
  simp [byteAtATime, Vec.mem_iff_mem_toList] at hmem
  rcases hmem with h | h | h <;> subst h <;> decide

/-- Three nonempty chunks deliver at least three bytes. -/
example : byteAtATime.length ≤ (Vec.flatten byteAtATime).length :=
  Vec.length_le_length_flatten byteAtATime_nonEmpty

/-- The degenerate chunking the rule excludes: any number of empty chunks
concatenate to nothing, so a reader counting chunks learns nothing about
progress. `Vec.AllNonEmpty` is false of it, which is the point. -/
def stalled : Vec (Vec Byte) :=
  Vec.fromList [Vec.empty, Vec.empty, Vec.empty]

example : Vec.flatten stalled = Vec.empty := rfl

example : ¬ Vec.AllNonEmpty stalled := by
  intro h
  exact h Vec.empty (by simp [stalled, Vec.mem_iff_mem_toList]) rfl

end Grass.Tests.Std.Chunking
