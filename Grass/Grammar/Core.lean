import Grass.Std.Logical.Vec

/-!
# Generic typed grammar vocabulary and byte consumers

This module is the first implementation slice of `docs/GRAMMAR.md`. It owns no
instruction-set fact. In particular, accepting a byte here is a generic format
operation; the predicate deciding whether an x86 opcode is meaningful remains
with `Grass.ISA.X86`.

The small executable consumers at the end establish two details on which every
binary reader depends: truncated input is `needMore`, not invalid, and success
returns the exact suffix. More elaborate parsers may replace their organization
but must realize the same relations.
-/

namespace Grass.Grammar

open Grass.Std.Logical

universe u v

/-- Stable, format-independent classes of syntactic failure.

Format-specific details are data attached by higher layers. `trailingInput` is
kept distinct from `malformed`: a prefix parser may lawfully return the suffix,
while a whole-input parser rejects it. -/
inductive ParseError where
  | malformed (context : String)
  | unsupported (context : String)
  | arithmeticOverflow (context : String)
  | trailingInput
deriving DecidableEq, Repr

/-- The precious three-way classification of a finite input buffer. -/
inductive ParseResult (α : Type u) where
  | done (value : α) (rest : Std.Logical.ByteArray)
  | needMore (minimumAdditional : Option Nat)
  | invalid (error : ParseError)

/-- A typed language description. Choice denotes the union of alternatives;
priority is never inferred from constructor order. This initial kernel contains
the constructors whose denotation is already used by the primitive consumers.
Further derived binary combinators belong above it. -/
inductive Format : Type → Type 1 where
  | pure {α : Type} (value : α) : Format α
  | byte (accepts : Byte → Prop) : Format Byte
  | seq {α β : Type} (left : Format α) (right : α → Format β) : Format (α × β)
  | choice {α : Type} (left right : Format α) : Format α
  | refine {α : Type} (inner : Format α) (accepts : α → Prop) : Format α

/-- Denotational parsing relation with an explicit unconsumed suffix. -/
inductive Derives : {α : Type} → Format α → Std.Logical.ByteArray → α →
    Std.Logical.ByteArray → Prop
  | pure {α : Type} (value : α) (input : Std.Logical.ByteArray) :
      Derives (.pure value) input value input
  | byte (accepts : Byte → Prop) (value : Byte) (rest : Std.Logical.ByteArray)
      (accepted : accepts value) :
      Derives (.byte accepts) (Vec.singleton value ++ rest) value rest
  | seq {α β : Type} {first : Format α} {next : α → Format β}
      {input middle rest : Std.Logical.ByteArray} {a : α} {b : β}
      (left : Derives first input a middle)
      (right : Derives (next a) middle b rest) :
      Derives (.seq first next) input (a, b) rest
  | choiceLeft {α : Type} {left right : Format α} {input rest : Std.Logical.ByteArray}
      {value : α} (derivation : Derives left input value rest) :
      Derives (.choice left right) input value rest
  | choiceRight {α : Type} {left right : Format α} {input rest : Std.Logical.ByteArray}
      {value : α} (derivation : Derives right input value rest) :
      Derives (.choice left right) input value rest
  | refine {α : Type} {inner : Format α} {predicate : α → Prop}
      {input rest : Std.Logical.ByteArray} {value : α}
      (derivation : Derives inner input value rest) (accepted : predicate value) :
      Derives (.refine inner predicate) input value rest

/-- Consume one byte. Empty input is repairable by exactly one byte. -/
def takeByte (input : Std.Logical.ByteArray) : ParseResult Byte :=
  match input.get? 0 with
  | none => .needMore (some 1)
  | some value => .done value (input.drop 1)

/-- Emit one byte in the canonical logical byte container. -/
def writeByte (value : Byte) : Std.Logical.ByteArray := Vec.singleton value

/-- A byte written in front of an arbitrary suffix is consumed with that exact
suffix. This is the prefix law used by sequencing parsers. -/
@[simp] theorem takeByte_writeByte_append (value : Byte) (rest : Std.Logical.ByteArray) :
    takeByte (writeByte value ++ rest) = .done value rest := by
  unfold takeByte writeByte
  rw [Vec.get?_append_left (by simp) rest]
  simp only [Vec.get?_singleton_zero]
  rw [Vec.drop_append_of_length_eq (by simp) rest]

/-- The whole-value round trip is the empty-suffix instance of the prefix law. -/
@[simp] theorem takeByte_writeByte (value : Byte) :
    takeByte (writeByte value) = .done value Vec.empty := by
  simpa using takeByte_writeByte_append value Vec.empty

/-- Every successful byte read consumed exactly the returned leading byte. -/
theorem takeByte_done {input : Std.Logical.ByteArray} {value : Byte}
    {rest : Std.Logical.ByteArray} (success : takeByte input = .done value rest) :
    input = Vec.singleton value ++ rest := by
  cases input with
  | fromList bytes =>
    cases bytes with
    | nil => simp [takeByte, Vec.get?] at success
    | cons first tail =>
      simp only [takeByte, Vec.get?, Vec.drop, List.getElem?_cons_zero] at success
      cases success
      rfl

/-- Exact-length consumption validates the length before taking or dropping.
The deficit is exact and uses natural subtraction, so no host-sized arithmetic
or unchecked index participates. -/
def takeExact (count : Nat) (input : Std.Logical.ByteArray) :
    ParseResult Std.Logical.ByteArray :=
  if count ≤ input.length then
    .done (input.take count) (input.drop count)
  else
    .needMore (some (count - input.length))

/-- An exact-length prefix is returned unchanged and leaves the exact suffix. -/
@[simp] theorem takeExact_append {head : Std.Logical.ByteArray} {count : Nat}
    (length : head.length = count) (rest : Std.Logical.ByteArray) :
    takeExact count (head ++ rest) = .done head rest := by
  simp [takeExact, Vec.length_append, length, Vec.take_append_of_length_eq,
    Vec.drop_append_of_length_eq]

/-- Taking zero bytes succeeds without consuming input, including empty input. -/
@[simp] theorem takeExact_zero (input : Std.Logical.ByteArray) :
    takeExact 0 input = .done Vec.empty input := by
  simp [takeExact]

/-- A short buffer is classified as repairable with its exact deficit. -/
theorem takeExact_short {count : Nat} {input : Std.Logical.ByteArray}
    (short : input.length < count) :
    takeExact count input = .needMore (some (count - input.length)) := by
  simp [takeExact, Nat.not_le.mpr short]

/-- Every successful exact-length consume makes progress by exactly `count` and
preserves all bytes through prefix/suffix recomposition. -/
theorem takeExact_done {count : Nat}
    {input value rest : Std.Logical.ByteArray}
    (success : takeExact count input = .done value rest) :
    value.length = count ∧ value ++ rest = input := by
  simp only [takeExact] at success
  split at success
  next enough =>
    cases success
    exact ⟨by simp [enough], Vec.append_splitAt input count⟩
  next short => contradiction

end Grass.Grammar
