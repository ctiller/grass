import Grass.Artifact.Binary.LEB128
import Grass.Artifact.Binary.LittleEndian

/-!
# Generic LEB128 vectors and length-prefixed sections

Two combinators every Wasm section reuses, independent of what a section
carries:

- `writeVec`/`readVec`: a Wasm `vec(elem)` — an LEB128 element count followed
  by that many elements back to back — generic over the element codec, so
  each section supplies only its own element reader/writer and gets the
  count-handling round trip for free (mirrors
  `Grass.ISA.Wasm.Target.decodeUVec_encode`, generalized past `Nat`
  elements).
- `writeSection`/`readSection`: one Wasm section — an id byte, an LEB128
  byte-length, then exactly that many content bytes — generic over the
  content itself.
-/

namespace Grass.Artifact.Wasm

open Grass.Artifact.Binary

/-- `vec(elem)`: an LEB128 count followed by that many elements. -/
def writeVec {α : Type} (elemWrite : α → List UInt8) (xs : List α) : List UInt8 :=
  natToLEB128 xs.length ++ (xs.map elemWrite).flatten

/-- Read exactly `n` consecutive elements from the head of the list. -/
def readVecN {α : Type} (elemRead : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes =>
      match elemRead bytes with
      | none => none
      | some (a, bytes) =>
          match readVecN elemRead n bytes with
          | none => none
          | some (as, rest) => some (a :: as, rest)

/-- Read a whole `vec(elem)`: an LEB128 count, then that many elements. -/
def readVec {α : Type} (elemRead : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (List α × List UInt8) :=
  match readLEB128 bytes with
  | none => none
  | some (n, bytes) => readVecN elemRead n bytes

/-- Reading back exactly `xs.length` elements with a correct element codec
recovers `xs` and the exact byte suffix. -/
theorem readVecN_writeVec {α : Type} (elemRead : List UInt8 → Option (α × List UInt8))
    (elemWrite : α → List UInt8)
    (roundtrip : ∀ (a : α) (rest : List UInt8), elemRead (elemWrite a ++ rest) = some (a, rest))
    (xs : List α) (rest : List UInt8) :
    readVecN elemRead xs.length ((xs.map elemWrite).flatten ++ rest) = some (xs, rest) := by
  induction xs generalizing rest with
  | nil => rfl
  | cons x xs ih =>
      have assoc : elemWrite x ++ (xs.map elemWrite).flatten ++ rest
          = elemWrite x ++ ((xs.map elemWrite).flatten ++ rest) := by
        simp [List.append_assoc]
      simp only [List.length_cons, List.map_cons, List.flatten_cons, assoc]
      rw [readVecN]
      simp only [roundtrip x, ih]

/-- The whole-vector round trip: a correct element codec makes `readVec`
invert `writeVec` exactly, whatever follows. -/
theorem readVec_writeVec {α : Type} (elemRead : List UInt8 → Option (α × List UInt8))
    (elemWrite : α → List UInt8)
    (roundtrip : ∀ (a : α) (rest : List UInt8), elemRead (elemWrite a ++ rest) = some (a, rest))
    (xs : List α) (rest : List UInt8) :
    readVec elemRead (writeVec elemWrite xs ++ rest) = some (xs, rest) := by
  unfold writeVec readVec
  rw [List.append_assoc, readLEB128_natToLEB128_append]
  exact readVecN_writeVec elemRead elemWrite roundtrip xs rest

/-- One Wasm section: an id byte, an LEB128 byte-length, then exactly that
many content bytes. -/
def writeSection (id : UInt8) (content : List UInt8) : List UInt8 :=
  id :: (natToLEB128 content.length ++ content)

/-- Read one section of the given `id`, refusing any other id (which is
exactly the "unknown sections" and "other orderings" rejection the artifact
format needs — a fixed, ascending section order is the only one `read`
accepts). Returns the section's own content and the byte suffix after it. -/
def readSection (id : UInt8) : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: bytes =>
      if b = id then
        match readLEB128 bytes with
        | none => none
        | some (size, bytes) => takeBytes size bytes
      else none

/-- The section-framing round trip: reading a section of its own id back
recovers exactly its content and the exact byte suffix. -/
theorem readSection_writeSection (id : UInt8) (content rest : List UInt8) :
    readSection id (writeSection id content ++ rest) = some (content, rest) := by
  unfold writeSection readSection
  simp only [List.cons_append]
  rw [List.append_assoc, readLEB128_natToLEB128_append]
  exact takeBytes_append_of_eq rfl

/-- One Wasm section holding `vec(elem)`: `writeSection`/`writeVec` composed
once, so every module-level section (`Grass.Artifact.Wasm.Target`) writes and
reads its element list without re-deriving this composition each time. -/
def writeSectionVec {α : Type} (id : UInt8) (elemWrite : α → List UInt8) (xs : List α) :
    List UInt8 :=
  writeSection id (writeVec elemWrite xs)

/-- Read a whole section as `vec(elem)`, requiring the element vector to
consume the section's content exactly (no trailing bytes within the
section) — this is the "other orderings"/trailing-garbage rejection this
seam's `read` needs, and it is automatic here since a canonical write never
leaves any. -/
def readSectionVec {α : Type} (id : UInt8) (elemRead : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (List α × List UInt8) :=
  match readSection id bytes with
  | none => none
  | some (content, rest) =>
      match readVec elemRead content with
      | some (xs, []) => some (xs, rest)
      | _ => none

/-- The section-vector round trip: a correct element codec makes
`readSectionVec` invert `writeSectionVec` exactly. -/
theorem readSectionVec_writeSectionVec {α : Type} (id : UInt8)
    (elemRead : List UInt8 → Option (α × List UInt8)) (elemWrite : α → List UInt8)
    (roundtrip : ∀ (a : α) (rest : List UInt8), elemRead (elemWrite a ++ rest) = some (a, rest))
    (xs : List α) (rest : List UInt8) :
    readSectionVec id elemRead (writeSectionVec id elemWrite xs ++ rest) = some (xs, rest) := by
  unfold writeSectionVec readSectionVec
  rw [readSection_writeSection]
  simp only
  have empty := readVec_writeVec elemRead elemWrite roundtrip xs []
  rw [List.append_nil] at empty
  rw [empty]

/-- The no-following-bytes instance, for the last section a module writes
(nothing appends an empty suffix there, so `readSectionVec_writeSectionVec`'s
`++ rest` does not syntactically match). -/
theorem readSectionVec_writeSectionVec_nil {α : Type} (id : UInt8)
    (elemRead : List UInt8 → Option (α × List UInt8)) (elemWrite : α → List UInt8)
    (roundtrip : ∀ (a : α) (rest : List UInt8), elemRead (elemWrite a ++ rest) = some (a, rest))
    (xs : List α) :
    readSectionVec id elemRead (writeSectionVec id elemWrite xs) = some (xs, []) := by
  simpa using readSectionVec_writeSectionVec id elemRead elemWrite roundtrip xs []

end Grass.Artifact.Wasm
