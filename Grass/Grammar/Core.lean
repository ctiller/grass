import Grass.Std.Logical.Vec

/-!
# Generic typed grammar vocabulary

This module is the first implementation slice of `docs/GRAMMAR.md`. It owns no
instruction-set fact. In particular, accepting a byte here is a generic format
operation; the predicate deciding whether an x86 opcode is meaningful remains
with `Grass.ISA.X86`.

Executable readers and writers live in `Grass.Artifact.Binary`; this module is
only the precious format and derivation vocabulary they realize.
-/

namespace Grass.Grammar

open Grass.Std.Logical

universe u v

/-- Stable, format-independent classes of syntactic failure. These classes are
precious; diagnostic strings attached by an implementation are not. -/
inductive ParseErrorClass where
  | malformed
  | unsupported
  | arithmeticOverflow
  | trailingInput
deriving DecidableEq, Repr

/-- A classified parse failure with non-precious diagnostic context.

Format-specific details are data attached by higher layers. `trailingInput` is
kept distinct from `malformed`: a prefix parser may lawfully return the suffix,
while a whole-input parser rejects it. -/
inductive ParseError where
  | malformed (context : String)
  | unsupported (context : String)
  | arithmeticOverflow (context : String)
  | trailingInput
deriving DecidableEq, Repr

/-- Project an implementation diagnostic to its precious failure class. -/
def ParseError.class : ParseError → ParseErrorClass
  | .malformed _ => .malformed
  | .unsupported _ => .unsupported
  | .arithmeticOverflow _ => .arithmeticOverflow
  | .trailingInput => .trailingInput

/-- The precious three-way classification of a finite input buffer. -/
inductive ParseResult (α : Type u) where
  | done (value : α) (rest : Std.Logical.ByteArray)
  | needMore (minimumAdditional : Option Nat)
  | invalid (error : ParseError)

/-- A proof-relevant, dependency-free isomorphism used by `Format.iso`. -/
structure Isomorphism (α β : Type) where
  forward : α → β
  backward : β → α
  backward_forward : ∀ value, backward (forward value) = value
  forward_backward : ∀ value, forward (backward value) = value

namespace Isomorphism

/-- Identity format isomorphism. -/
def refl (α : Type) : Isomorphism α α where
  forward := id
  backward := id
  backward_forward _ := rfl
  forward_backward _ := rfl

end Isomorphism

/-- A typed language description. Choice denotes the union of alternatives;
priority is never inferred from constructor order. This initial kernel contains
the constructors whose denotation is already used by the primitive consumers.
Further derived binary combinators belong above it. -/
inductive Format : Type → Type 1 where
  | pure {α : Type} (value : α) : Format α
  | byte (accepts : Byte → Prop) : Format Byte
  | seq {α β : Type} (left : Format α) (right : α → Format β) : Format (α × β)
  | choice {α : Type} (left right : Format α) : Format α
  | repeat {α : Type} (count : Nat) (item : Format α) : Format (Vec α)
  | refine {α : Type} (inner : Format α) (accepts : α → Prop) : Format α
  | lift {α β : Type} (inner : Format α) (forget : β → α) : Format β
  | iso {α β : Type} (inner : Format α)
      (isomorphism : Isomorphism α β) : Format β

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
  | repeatZero {α : Type} (item : Format α) (input : Std.Logical.ByteArray) :
      Derives (.repeat 0 item) input Vec.empty input
  | repeatSucc {α : Type} {count : Nat} {item : Format α}
      {input middle rest : Std.Logical.ByteArray} {value : α} {values : Vec α}
      (head : Derives item input value middle)
      (tail : Derives (.repeat count item) middle values rest) :
      Derives (.repeat (Nat.succ count) item) input (Vec.singleton value ++ values) rest
  | refine {α : Type} {inner : Format α} {predicate : α → Prop}
      {input rest : Std.Logical.ByteArray} {value : α}
      (derivation : Derives inner input value rest) (accepted : predicate value) :
      Derives (.refine inner predicate) input value rest
  | lift {α β : Type} {inner : Format α} {forget : β → α}
      {input rest : Std.Logical.ByteArray} {value : β}
      (derivation : Derives inner input (forget value) rest) :
      Derives (.lift inner forget) input value rest
  | iso {α β : Type} {inner : Format α} {isomorphism : Isomorphism α β}
      {input rest : Std.Logical.ByteArray} {value : α}
      (derivation : Derives inner input value rest) :
      Derives (.iso inner isomorphism) input (isomorphism.forward value) rest

namespace Derives

/-- The outer format constructor determines the corresponding derivation
shape. This dependent helper supports constructor-specific inversion without
assuming any executable parser. -/
theorem outerShape {α : Type} {format : Format α}
    {input : Std.Logical.ByteArray} {value : α}
    {rest : Std.Logical.ByteArray}
    (derivation : Derives format input value rest) :
    match format with
    | .byte accepts =>
        input = Vec.singleton value ++ rest ∧ accepts value
    | _ => True := by
  induction derivation <;> simp_all

/-- A byte-format derivation consumes exactly its leading byte. -/
theorem byteInput {accepts : Byte → Prop} {input : Std.Logical.ByteArray}
    {value : Byte} {rest : Std.Logical.ByteArray}
    (derivation : Derives (.byte accepts) input value rest) :
    input = Vec.singleton value ++ rest :=
  (outerShape derivation).1

/-- A byte-format derivation carries the format's acceptance proof. -/
theorem byteAccepted {accepts : Byte → Prop} {input : Std.Logical.ByteArray}
    {value : Byte} {rest : Std.Logical.ByteArray}
    (derivation : Derives (.byte accepts) input value rest) : accepts value :=
  (outerShape derivation).2

/-- Every derivation consumes a prefix and retains the exact remaining suffix. -/
theorem consumesPrefix {α : Type} {format : Format α}
    {input : Std.Logical.ByteArray} {value : α}
    {rest : Std.Logical.ByteArray}
    (derivation : Derives format input value rest) :
    ∃ consumed, input = consumed ++ rest := by
  induction derivation with
  | pure value input => exact ⟨Vec.empty, by simp⟩
  | byte accepts value rest accepted => exact ⟨Vec.singleton value, rfl⟩
  | seq left right leftPrefix rightPrefix =>
      rcases leftPrefix with ⟨leftBytes, rfl⟩
      rcases rightPrefix with ⟨rightBytes, rfl⟩
      exact ⟨leftBytes ++ rightBytes, by simp [Vec.append_assoc]⟩
  | choiceLeft derivation choicePrefix => exact choicePrefix
  | choiceRight derivation choicePrefix => exact choicePrefix
  | repeatZero item input => exact ⟨Vec.empty, by simp⟩
  | repeatSucc head tail headPrefix tailPrefix =>
      rcases headPrefix with ⟨headBytes, rfl⟩
      rcases tailPrefix with ⟨tailBytes, rfl⟩
      exact ⟨headBytes ++ tailBytes, by simp [Vec.append_assoc]⟩
  | refine derivation accepted refinedPrefix => exact refinedPrefix
  | lift derivation liftedPrefix => exact liftedPrefix
  | iso derivation mappedPrefix => exact mappedPrefix

/-- The outer repeat constructor exposes its exact fixed-item consumption law
without requiring unsafe inversion of `Format`'s result-type index. -/
theorem repeatConsumedLengthShape {α : Type} {format : Format α}
    {input : Std.Logical.ByteArray} {value : α} {rest : Std.Logical.ByteArray}
    (derivation : Derives format input value rest) :
    match format with
    | .repeat count item => ∀ itemWidth,
        (∀ {itemInput itemValue itemRest},
          Derives item itemInput itemValue itemRest →
            itemInput.length = itemWidth + itemRest.length) →
        input.length = count * itemWidth + rest.length
    | _ => True := by
  induction derivation with
  | pure => trivial
  | byte => trivial
  | seq => trivial
  | choiceLeft => trivial
  | choiceRight => trivial
  | repeatZero => simp
  | repeatSucc head tail _ tailLength =>
      simp only
      intro itemWidth itemLength
      have headLength := itemLength head
      have remainingLength := tailLength itemWidth itemLength
      rw [Nat.succ_mul]
      omega
  | refine => trivial
  | lift => trivial
  | iso => trivial

/-- Expose the head and tail of a repeated-format derivation while preserving
the result-type index. This is the value-level companion to
`repeatConsumedLengthShape`. -/
theorem repeatOuterShape {α : Type} {format : Format α}
    {input : Std.Logical.ByteArray} {value : α} {rest : Std.Logical.ByteArray}
    (derivation : Derives format input value rest) :
    match format with
    | .repeat 0 item => value = Vec.empty ∧ input = rest
    | .repeat (Nat.succ count) item =>
        ∃ middle head tail,
          value = Vec.singleton head ++ tail ∧
          Derives item input head middle ∧
          Derives (.repeat count item) middle tail rest
    | _ => True := by
  induction derivation with
  | pure => trivial
  | byte => trivial
  | seq => trivial
  | choiceLeft => trivial
  | choiceRight => trivial
  | repeatZero => exact ⟨rfl, rfl⟩
  | repeatSucc head tail => exact ⟨_, _, _, rfl, head, tail⟩
  | refine => trivial
  | lift => trivial
  | iso => trivial

/-- Prefix-format derivations are stable under an arbitrary appended suffix.
The parsed value is unchanged and the exact residual bytes gain that suffix.
This is the semantic transport law that lets concrete writers compose without
revealing their implementations. -/
theorem appendSuffix {α : Type} {format : Format α}
    {input : Std.Logical.ByteArray} {value : α}
    {rest : Std.Logical.ByteArray}
    (derivation : Derives format input value rest)
    (suffix : Std.Logical.ByteArray) :
    Derives format (input ++ suffix) value (rest ++ suffix) := by
  induction derivation with
  | pure value input => exact Derives.pure value (input ++ suffix)
  | byte accepts value rest accepted =>
      simpa [Vec.append_assoc] using
        Derives.byte accepts value (rest ++ suffix) accepted
  | seq left right leftSuffix rightSuffix =>
      exact Derives.seq leftSuffix rightSuffix
  | choiceLeft derivation derivationSuffix =>
      exact Derives.choiceLeft derivationSuffix
  | choiceRight derivation derivationSuffix =>
      exact Derives.choiceRight derivationSuffix
  | repeatZero item input => exact Derives.repeatZero item (input ++ suffix)
  | repeatSucc head tail headSuffix tailSuffix =>
      exact Derives.repeatSucc headSuffix tailSuffix
  | refine derivation accepted derivationSuffix =>
      exact Derives.refine derivationSuffix accepted
  | lift derivation derivationSuffix =>
      exact Derives.lift derivationSuffix
  | iso derivation derivationSuffix =>
      exact Derives.iso derivationSuffix

/-- Concatenate a complete left encoding with a right encoding and derive their
sequence without exposing either writer implementation. The empty residual on
the left is essential: it is replaced by the entire right input using
`appendSuffix`, after which the ordinary `Derives.seq` constructor applies. -/
theorem seqAppend {α β : Type} {first : Format α} {next : α → Format β}
    {leftInput rightInput rest : Std.Logical.ByteArray} {leftValue : α}
    {rightValue : β}
    (left : Derives first leftInput leftValue Vec.empty)
    (right : Derives (next leftValue) rightInput rightValue rest) :
    Derives (.seq first next) (leftInput ++ rightInput)
      (leftValue, rightValue) rest := by
  exact Derives.seq (by simpa using left.appendSuffix rightInput) right

end Derives

/-- Eliminate one value-lifting derivation back to the underlying format. -/
theorem Derives.lift_inner {α β : Type} {inner : Format α}
    {forget : β → α} {input rest : Std.Logical.ByteArray} {value : β}
    (derivation : Derives (.lift inner forget) input value rest) :
    Derives inner input (forget value) rest := by
  cases derivation with
  | lift innerDerivation => exact innerDerivation

/-- Eliminate an isomorphism derivation back to its underlying value. -/
theorem Derives.iso_inner {α β : Type} {inner : Format α}
    {isomorphism : Isomorphism α β} {input rest : Std.Logical.ByteArray}
    {value : β} (derivation : Derives (.iso inner isomorphism) input value rest) :
    Derives inner input (isomorphism.backward value) rest := by
  cases derivation with
  | iso innerDerivation =>
      simpa only [isomorphism.backward_forward] using innerDerivation

/-- Promote a value invariant into the public result type of a format. This is
distinct from `Format.refine`, which filters while retaining the same value
type. -/
def Format.refineValue {α : Type} (inner : Format α) (accepts : α → Prop) :
    Format {value // accepts value} :=
  .lift inner Subtype.val

/-- Denotational equation for invariant-promoting refinement. -/
theorem derives_refineValue_iff {α : Type} {inner : Format α}
    {accepts : α → Prop} {input rest : Std.Logical.ByteArray}
    {value : α} (accepted : accepts value) :
    Derives (inner.refineValue accepts) input ⟨value, accepted⟩ rest ↔
      Derives inner input value rest := by
  constructor
  · intro derivation
    exact derivation.lift_inner
  · intro innerDerivation
    exact Derives.lift innerDerivation

end Grass.Grammar
