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

end Grass.Grammar
