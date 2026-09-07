import Grass.Construct.Source.Ast

/-!
# Explicitly tainted unchecked construction

Unchecked authored syntax remains ordinary inspectable data, but it is wrapped
with a nonempty structured taint record. This module provides no certificate,
verification cast, or promotion function; checked lowering continues to require
`Grass.Construct.Source.VerifiedAst`.
-/

namespace Grass.Unsafe

open Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

universe u v w x

/-- Why an unchecked authored value entered the raw boundary. -/
inductive TaintKind where
  | uncheckedConstruction
  | importedBytes
  | unresolvedControlFlow
  | externalGenerator
  | userOverride
deriving Repr, DecidableEq

/-- One review-visible reason an authored value is not certificate-bearing. -/
structure Taint where
  kind : TaintKind
  detail : String
deriving Repr, DecidableEq

/-- An authored AST accompanied by at least one explicit taint.

The wrapped AST may be malformed. Possessing this value confers no
`Ast.WellFormed` or `VerifiedAst` evidence. -/
structure UncheckedAst (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) where
  source : Ast State Terminal Instruction Annotation
  primaryTaint : Taint
  additionalTaints : List Taint := []

namespace UncheckedAst

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Every taint in stable review order, beginning with the mandatory reason. -/
def taints (raw : UncheckedAst State Terminal Instruction Annotation) : List Taint :=
  raw.primaryTaint :: raw.additionalTaints

/-- `UncheckedAst.taints_ne_nil` proves the explicit taint ledger is nonempty. -/
theorem taints_ne_nil (raw : UncheckedAst State Terminal Instruction Annotation) :
    raw.taints ≠ [] := by
  simp [taints]

/-- Add a further taint without changing the wrapped authored source. -/
def addTaint (raw : UncheckedAst State Terminal Instruction Annotation)
    (taint : Taint) : UncheckedAst State Terminal Instruction Annotation :=
  { raw with additionalTaints := raw.additionalTaints ++ [taint] }

@[simp] theorem addTaint_source
    (raw : UncheckedAst State Terminal Instruction Annotation) (taint : Taint) :
    (raw.addTaint taint).source = raw.source := rfl

@[simp] theorem addTaint_taints
    (raw : UncheckedAst State Terminal Instruction Annotation) (taint : Taint) :
    (raw.addTaint taint).taints = raw.taints ++ [taint] := by
  simp [addTaint, taints]

end UncheckedAst

/-- Construct an unchecked block without claiming contract or edge closure. -/
def uncheckedBlock {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    (cfg : CFG.Block State Terminal) (body : Source Instruction)
    (annotations : List Annotation := []) :
    Grass.Construct.Source.Block State Terminal Instruction Annotation :=
  ⟨cfg, body, annotations⟩

/-- Construct a visibly tainted AST without running a structural checker. -/
def uncheckedAst {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    (entry : BlockId)
    (blocks : List (Grass.Construct.Source.Block State Terminal Instruction Annotation))
    (taint : Taint) (additionalTaints : List Taint := []) :
    UncheckedAst State Terminal Instruction Annotation :=
  ⟨⟨entry, blocks⟩, taint, additionalTaints⟩

end Grass.Unsafe
