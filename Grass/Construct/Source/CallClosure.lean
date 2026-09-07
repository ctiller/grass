import Grass.CFG.Compose
import Grass.Construct.Source.Discover

/-!
# Authored call-site closure

`AuthoredCallSource` derives call occurrences from exact located instruction
expansion through one explicit projection. `checkAuthoredCalls` checks the
source graph first, then requires each call target and return target to resolve
and each call to be the sole projection of the block's final instruction, with
its return family equal to the containing block's actual outgoing edges.
Exact equality between the block and call contracts remains the separate
proof-bearing `CertifiedAuthoredCallSource.exact` field.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- One authored AST and its exact instruction-to-call projection. -/
structure AuthoredCallSource (State : Type u) (Terminal : Type v)
    (Instruction : Type w) (Annotation : Type x) where
  ast : Ast State Terminal Instruction Annotation
  model : ManifestModel Instruction (CallSite State Terminal)

/-- Stable diagnostic key for one call occurrence that fails structural closure. -/
structure LocatedCallKey (Terminal : Type v) where
  block : BlockId
  origin : SourceOrigin
  projectedIndex : Nat
  target : CallTarget
  returns : List (CallReturn Terminal)
deriving Repr, DecidableEq

namespace AuthoredCallSource

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Exact located call occurrences derived from instruction expansion. -/
def occurrences
    (source : AuthoredCallSource State Terminal Instruction Annotation) :
    List (LocatedItem (CallSite State Terminal)) :=
  source.ast.discoverItems source.model

/-- Whether one derived call is routed by its exact containing CFG block. -/
def occurrenceClosed
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation)
    (located : LocatedItem (CallSite State Terminal)) : Bool :=
  match source.ast.findBlock? located.block with
  | none => false
  | some block =>
      located.item.closedIn source.ast.toGraph &&
        decide (block.cfg.outgoing = located.item.returnEdges) &&
        decide (located.projectedIndex = 0) &&
        decide (block.body.expandLocated.getLast?.map
          LocatedInstruction.origin = some located.origin)

/-- Structurally invalid call occurrences in exact discovered order. -/
def unclosed
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation) :
    List (LocatedCallKey Terminal) :=
  source.occurrences.filterMap fun located =>
    if source.occurrenceClosed located then none
    else some ⟨located.block, located.origin, located.projectedIndex,
      located.item.target, located.item.returns⟩

/-- Structural graph closure plus closure of every exact derived call occurrence. -/
def WellFormed
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation) : Prop :=
  source.ast.WellFormed ∧
    (source.occurrences.all source.occurrenceClosed) = true

instance
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation) :
    Decidable source.WellFormed := by
  unfold WellFormed
  infer_instance

/-- `AuthoredCallSource.Exact` supplies proof-bearing call-contract equality. -/
def Exact
    (source : AuthoredCallSource State Terminal Instruction Annotation) : Prop :=
  ∀ located ∈ source.occurrences,
    ∃ block,
      source.ast.findBlock? located.block = some block ∧
      block.cfg.contract = located.item.contract.toBlockContract

/-- Derived occurrences project exactly to the source's call manifest. -/
theorem occurrencesExact
    (source : AuthoredCallSource State Terminal Instruction Annotation) :
    source.occurrences.map LocatedItem.item =
      source.ast.itemManifest source.model :=
  source.ast.discoveredItems_exact source.model

/-- A successful structural call source has no unclosed call diagnostic. -/
theorem unclosed_eq_nil
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation)
    (valid : source.WellFormed) : source.unclosed = [] := by
  unfold unclosed
  rw [List.filterMap_eq_nil_iff]
  intro located hlocated
  have hall := List.all_eq_true.mp valid.2 located hlocated
  simp [hall]

end AuthoredCallSource

/-- Authored call source with executable structural closure evidence. -/
structure CheckedAuthoredCallSource
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation) :
    Type (max u v w x) where
  valid : source.WellFormed

/-- Checked calls plus exact proof-bearing block/call contract correspondence. -/
structure CertifiedAuthoredCallSource
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation) :
    Type (max u v w x) where
  checked : CheckedAuthoredCallSource source
  exact : source.Exact

/-- Stage-specific authored call-closure rejection. -/
inductive AuthoredCallError (Terminal : Type v) where
  | structural (entry : BlockId) (blocks : List BlockId)
  | calls (unclosed : List (LocatedCallKey Terminal))
deriving Repr, DecidableEq

/-- Check graph closure before checking exact derived call routing. -/
def checkAuthoredCalls
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x}
    [DecidableEq Terminal]
    (source : AuthoredCallSource State Terminal Instruction Annotation) :
    Except (AuthoredCallError Terminal) (CheckedAuthoredCallSource source) :=
  if structural : source.ast.WellFormed then
    if calls : source.occurrences.all source.occurrenceClosed = true then
      .ok ⟨structural, calls⟩
    else .error (.calls source.unclosed)
  else .error (.structural source.ast.entry source.ast.blockIds)

end Grass.Construct.Source
