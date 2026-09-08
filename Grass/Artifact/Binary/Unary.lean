import Grass.Artifact.Binary.Realization

/-!
# Canonical unary natural-number reader and writer

This executable pair realizes the generic marker-delimited natural-number
format in `Grass.Grammar.Binary`.  The `.gobj` scope codec consumes it as a
framing primitive rather than defining a format-specific length parser.
-/

namespace Grass.Artifact.Binary

open Grass.Grammar Grass.Std.Logical

/-- Write `count` continuation bytes and one terminator. -/
def writeUnaryNat (count : Nat) : Std.Logical.ByteArray :=
  Vec.replicate count 1 ++ Vec.singleton 0

/-- Read a unary prefix while retaining the number of consumed continuations. -/
def readUnaryNatList : List Byte → Nat → ParseResult Nat
  | [], _ => .needMore (some 1)
  | byte :: rest, count =>
      if byte = 1 then
        readUnaryNatList rest (count + 1)
      else if byte = 0 then
        .done count (Vec.fromList rest)
      else
        .invalid (.malformed "noncanonical unary natural")

/-- Read the canonical unary natural at the front of a logical byte sequence. -/
def readUnaryNat (input : Std.Logical.ByteArray) : ParseResult Nat :=
  readUnaryNatList input.toList 0

/-- `length_writeUnaryNat` pins the exact continuation-plus-terminator width. -/
@[simp] theorem length_writeUnaryNat (count : Nat) :
    (writeUnaryNat count).length = count + 1 := by
  simp [writeUnaryNat]

@[simp] theorem readUnaryNatList_replicate (count offset : Nat)
    (suffix : List Byte) :
    readUnaryNatList (List.replicate count 1 ++ 0 :: suffix) offset =
      .done (offset + count) (Vec.fromList suffix) := by
  induction count generalizing offset with
  | zero => simp [readUnaryNatList]
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, readUnaryNatList,
        if_pos]
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- `readUnaryNat_write_append` proves exact recovery with suffix custody. -/
@[simp] theorem readUnaryNat_write_append (count : Nat)
    (suffix : Std.Logical.ByteArray) :
    readUnaryNat (writeUnaryNat count ++ suffix) = .done count suffix := by
  cases suffix with
  | fromList bytes =>
      unfold readUnaryNat writeUnaryNat
      rw [Vec.toList_append, Vec.toList_append]
      change readUnaryNatList
        (List.replicate count 1 ++ [0] ++ bytes) 0 =
          .done count (Vec.fromList bytes)
      simpa using readUnaryNatList_replicate count 0 bytes

/-- `writeUnaryNat_derives` connects the executable writer to the independent
generic format without appealing to the reader round trip. -/
theorem writeUnaryNat_derives (count : Nat) :
    Derives unaryNatFormat (writeUnaryNat count) count Vec.empty := by
  unfold writeUnaryNat
  simpa using unaryNat_derives count Vec.empty

end Grass.Artifact.Binary
