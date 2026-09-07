import Grass.Construct.Lower
import Grass.Unsafe.Raw

/-!
# Checked-lowering erasure

`RawHierarchy.ofLowered` erases a checked Construct lowering to its instruction
projection, canonicalizing an empty result to `RawHierarchy.empty`.
`RawHierarchy.flatten_ofVerifiedAst` ties the unsafe writer input back to the
exact authored block-order expansion.
-/

namespace Grass.Unsafe

open Grass.Construct.Fragment Grass.Construct.Source

universe u v w x y

namespace RawHierarchy

/-- Erase complete checked lowering output to a raw writer hierarchy. -/
def ofLowered {State : Type u} {Terminal : Type v} {Instruction : Type w}
    (lowered : LoweredProgram State Terminal Instruction) : RawHierarchy Instruction :=
  match lowered.items.map LoweredInstruction.instruction with
  | [] => .empty
  | instructions@(_ :: _) => .leaf instructions

/-- `RawHierarchy.flatten_ofLowered` states that raw erasure preserves the
checked lowered instruction projection exactly. -/
@[simp] theorem flatten_ofLowered
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    (lowered : LoweredProgram State Terminal Instruction) :
    (ofLowered lowered).flatten = lowered.items.map LoweredInstruction.instruction := by
  unfold ofLowered
  split <;> simp_all

/-- Erase one verified authored AST through its checked lowering. -/
def ofVerifiedAst {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {source : Ast State Terminal Instruction Annotation}
    (verified : VerifiedAst semantics effectModel source) : RawHierarchy Instruction :=
  ofLowered verified.lower

/-- The unsafe hierarchy for a verified AST flattens to the exact authored
block-order instruction expansion. -/
theorem flatten_ofVerifiedAst
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    {source : Ast State Terminal Instruction Annotation}
    (verified : VerifiedAst semantics effectModel source) :
    (ofVerifiedAst verified).flatten = source.instructions := by
  rw [ofVerifiedAst, flatten_ofLowered]
  exact VerifiedAst.lower_instructions_exact verified

end RawHierarchy

end Grass.Unsafe
