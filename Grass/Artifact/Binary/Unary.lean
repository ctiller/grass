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

/-- Successful list-level unary parsing is exactly a run of continuation
markers followed by the terminator and the returned suffix. -/
theorem readUnaryNatList_done_iff (bytes : List Byte) (offset value : Nat)
    (rest : Std.Logical.ByteArray) :
    readUnaryNatList bytes offset = .done value rest ↔
      ∃ count, bytes = List.replicate count 1 ++ 0 :: rest.toList ∧
        value = offset + count := by
  induction bytes generalizing offset value rest with
  | nil => simp [readUnaryNatList]
  | cons byte tail inductionHypothesis =>
      by_cases isMore : byte = 1
      · subst byte
        simp only [readUnaryNatList, if_pos]
        rw [inductionHypothesis]
        constructor
        · rintro ⟨count, tailShape, rfl⟩
          refine ⟨Nat.succ count, ?_, by omega⟩
          simp [List.replicate_succ, tailShape]
        · rintro ⟨count, shape, valueShape⟩
          cases count with
          | zero => simp at shape
          | succ count =>
              simp only [List.replicate_succ, List.cons_append,
                List.cons.injEq] at shape
              exact ⟨count, shape.2, by omega⟩
      · by_cases isStop : byte = 0
        · subst byte
          simp only [readUnaryNatList, if_neg isMore, if_pos]
          constructor
          · intro parsed
            injection parsed with valueEq restEq
            refine ⟨0, ?_, by omega⟩
            simp only [List.replicate_zero, List.nil_append,
              List.cons.injEq, true_and]
            have lists := congrArg Vec.toList restEq
            simpa using lists
          · rintro ⟨count, shape, valueShape⟩
            cases count with
            | zero =>
                simp only [List.replicate_zero, List.nil_append,
                  List.cons.injEq, true_and] at shape
                have restEq : Vec.fromList tail = rest := by
                  apply Vec.toList_injective
                  simpa using shape
                subst value
                exact congrArg (ParseResult.done offset) restEq
            | succ count =>
                simp only [List.replicate_succ, List.cons_append,
                  List.cons.injEq] at shape
                exact False.elim (isMore shape.1)

        · rw [readUnaryNatList, if_neg isMore, if_neg isStop]
          constructor
          · intro parsed
            contradiction
          · rintro ⟨count, shape, _⟩
            cases count with
            | zero =>
                simp only [List.replicate_zero, List.nil_append,
                  List.cons.injEq] at shape
                exact False.elim (isStop shape.1)
            | succ count =>
                simp only [List.replicate_succ, List.cons_append,
                  List.cons.injEq] at shape
                exact False.elim (isMore shape.1)

/-- Arbitrary successful unary parsing is exactly the independent unary format
derivation with the returned suffix. -/
theorem readUnaryNat_done_iff (input : Std.Logical.ByteArray) (value : Nat)
    (rest : Std.Logical.ByteArray) :
    readUnaryNat input = .done value rest ↔
      Derives unaryNatFormat input value rest := by
  unfold readUnaryNat
  rw [readUnaryNatList_done_iff]
  rw [derives_unaryNatFormat_iff]
  constructor
  · rintro ⟨count, listShape, valueShape⟩
    have countEq : value = count := by omega
    subst value
    apply Vec.toList_injective
    simpa [Vec.replicate, Vec.singleton] using listShape
  · intro shape
    refine ⟨value, ?_, by omega⟩
    have lists := congrArg Vec.toList shape
    simpa [Vec.replicate, Vec.singleton] using lists

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
