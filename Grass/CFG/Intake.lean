import Grass.CFG.Graph

/-!
# Structural CFG intake

This module defines the construction-owned target of an upstream lowering
adapter. Upstream entry and step identities stay opaque: an adapter supplies
their exact bindings to graph blocks and canonical edges, while this layer
checks only structural closure. It does not claim that an upstream process,
state machine, or specification is realized by the graph.
-/

namespace Grass.CFG

universe u v e s

/-- One opaque upstream entry identity bound to an authored CFG block. -/
structure IntakeEntry (EntryId : Type e) where
  source : EntryId
  block : BlockId
deriving Repr, DecidableEq

/-- One opaque upstream step identity bound to an authored CFG edge. -/
structure IntakeStep (StepId : Type s) where
  source : StepId
  edge : EdgeKey
deriving Repr, DecidableEq

/-- Exact structural bindings supplied by an upstream-to-CFG adapter. -/
structure AuthoredCFGIntake (EntryId : Type e) (StepId : Type s)
    {State : Type u} {Terminal : Type v} (graph : Graph State Terminal) where
  entries : List (IntakeEntry EntryId)
  steps : List (IntakeStep StepId)

namespace AuthoredCFGIntake

variable {EntryId : Type e} {StepId : Type s}
  {State : Type u} {Terminal : Type v} {graph : Graph State Terminal}
  [DecidableEq EntryId] [DecidableEq StepId]

/-- Upstream entry identities in adapter order. -/
def entryIds (intake : AuthoredCFGIntake EntryId StepId graph) : List EntryId :=
  intake.entries.map IntakeEntry.source

/-- Upstream step identities in adapter order. -/
def stepIds (intake : AuthoredCFGIntake EntryId StepId graph) : List StepId :=
  intake.steps.map IntakeStep.source

/-- Every entry binding names a structural graph block. -/
def EntriesResolved (intake : AuthoredCFGIntake EntryId StepId graph) : Prop :=
  ∀ binding ∈ intake.entries, binding.block ∈ graph.blockIds

/-- Every step binding names a canonical structural graph edge. -/
def StepsResolved (intake : AuthoredCFGIntake EntryId StepId graph) : Prop :=
  ∀ binding ∈ intake.steps, binding.edge ∈ graph.edgeKeys

/-- Find one entry binding by its opaque upstream identity. -/
def findEntry? (intake : AuthoredCFGIntake EntryId StepId graph)
    (source : EntryId) : Option (IntakeEntry EntryId) :=
  intake.entries.find? fun binding => binding.source == source

/-- Find one step binding by its opaque upstream identity. -/
def findStep? (intake : AuthoredCFGIntake EntryId StepId graph)
    (source : StepId) : Option (IntakeStep StepId) :=
  intake.steps.find? fun binding => binding.source == source

/-- Executable structural closure check for an upstream adapter result. -/
def wellFormed (intake : AuthoredCFGIntake EntryId StepId graph) : Bool :=
  graph.wellFormed &&
  decide intake.entryIds.Nodup &&
  decide intake.stepIds.Nodup &&
  intake.entries.all (fun binding => graph.blockIds.contains binding.block) &&
  intake.steps.all (fun binding => graph.edgeKeys.contains binding.edge)

/-- Certificate-facing structural closure of upstream CFG bindings. -/
def WellFormed (intake : AuthoredCFGIntake EntryId StepId graph) : Prop :=
  intake.wellFormed = true

instance (intake : AuthoredCFGIntake EntryId StepId graph) :
    Decidable intake.WellFormed :=
  inferInstanceAs (Decidable (intake.wellFormed = true))

/-- Public proposition-level decomposition of structural intake closure. -/
@[simp] theorem wellFormed_iff
    (intake : AuthoredCFGIntake EntryId StepId graph) :
    intake.WellFormed ↔
      (((graph.WellFormed ∧ intake.entryIds.Nodup) ∧ intake.stepIds.Nodup) ∧
        intake.EntriesResolved) ∧ intake.StepsResolved := by
  simp [WellFormed, wellFormed, Graph.WellFormed, EntriesResolved, StepsResolved]

theorem graphWellFormed_of_wellFormed
    (intake : AuthoredCFGIntake EntryId StepId graph) (h : intake.WellFormed) :
    graph.WellFormed :=
  (wellFormed_iff intake).mp h |>.1.1.1.1

theorem entryIdsNodup_of_wellFormed
    (intake : AuthoredCFGIntake EntryId StepId graph) (h : intake.WellFormed) :
    intake.entryIds.Nodup :=
  (wellFormed_iff intake).mp h |>.1.1.1.2

theorem stepIdsNodup_of_wellFormed
    (intake : AuthoredCFGIntake EntryId StepId graph) (h : intake.WellFormed) :
    intake.stepIds.Nodup :=
  (wellFormed_iff intake).mp h |>.1.1.2

theorem entriesResolved_of_wellFormed
    (intake : AuthoredCFGIntake EntryId StepId graph) (h : intake.WellFormed) :
    intake.EntriesResolved :=
  (wellFormed_iff intake).mp h |>.1.2

theorem stepsResolved_of_wellFormed
    (intake : AuthoredCFGIntake EntryId StepId graph) (h : intake.WellFormed) :
    intake.StepsResolved :=
  (wellFormed_iff intake).mp h |>.2

omit [DecidableEq StepId] in
theorem findEntry?_sound
    (intake : AuthoredCFGIntake EntryId StepId graph) (source : EntryId)
    (binding : IntakeEntry EntryId)
    (hfind : intake.findEntry? source = some binding) :
    binding ∈ intake.entries ∧ binding.source = source := by
  constructor
  · exact List.mem_of_find?_eq_some (by simpa [findEntry?] using hfind)
  · have matched : binding.source == source := List.find?_some
      (p := fun candidate : IntakeEntry EntryId => candidate.source == source) (by
        simpa [findEntry?] using hfind)
    exact LawfulBEq.eq_of_beq matched

omit [DecidableEq EntryId] in
theorem findStep?_sound
    (intake : AuthoredCFGIntake EntryId StepId graph) (source : StepId)
    (binding : IntakeStep StepId)
    (hfind : intake.findStep? source = some binding) :
    binding ∈ intake.steps ∧ binding.source = source := by
  constructor
  · exact List.mem_of_find?_eq_some (by simpa [findStep?] using hfind)
  · have matched : binding.source == source := List.find?_some
      (p := fun candidate : IntakeStep StepId => candidate.source == source) (by
        simpa [findStep?] using hfind)
    exact LawfulBEq.eq_of_beq matched

omit [DecidableEq StepId] in
@[simp] theorem findEntry?_isSome_iff_mem_entryIds
    (intake : AuthoredCFGIntake EntryId StepId graph) (source : EntryId) :
    (intake.findEntry? source).isSome = true ↔ source ∈ intake.entryIds := by
  simp [findEntry?, entryIds]

omit [DecidableEq EntryId] in
@[simp] theorem findStep?_isSome_iff_mem_stepIds
    (intake : AuthoredCFGIntake EntryId StepId graph) (source : StepId) :
    (intake.findStep? source).isSome = true ↔ source ∈ intake.stepIds := by
  simp [findStep?, stepIds]

/-- `AuthoredCFGIntake.blockForEntry` returns both the adapter binding and the
concrete graph block selected for a declared upstream entry. -/
theorem blockForEntry
    (intake : AuthoredCFGIntake EntryId StepId graph) (h : intake.WellFormed)
    (source : EntryId) (member : source ∈ intake.entryIds) :
    ∃ binding block,
      intake.findEntry? source = some binding ∧
      graph.findBlock? binding.block = some block := by
  rcases Option.isSome_iff_exists.mp
      ((intake.findEntry?_isSome_iff_mem_entryIds source).2 member) with
    ⟨binding, found⟩
  have blockMember : binding.block ∈ graph.blockIds :=
    intake.entriesResolved_of_wellFormed h binding
      (intake.findEntry?_sound source binding found).1
  rcases graph.blockForId binding.block blockMember with ⟨block, blockFound⟩
  exact ⟨binding, block, found, blockFound⟩

/-- `AuthoredCFGIntake.edgeForStep` returns both the adapter binding and the
concrete located graph edge selected for a declared upstream step. -/
theorem edgeForStep
    (intake : AuthoredCFGIntake EntryId StepId graph) (h : intake.WellFormed)
    (source : StepId) (member : source ∈ intake.stepIds) :
    ∃ binding located,
      intake.findStep? source = some binding ∧
      graph.findEdge? binding.edge = some located := by
  rcases Option.isSome_iff_exists.mp
      ((intake.findStep?_isSome_iff_mem_stepIds source).2 member) with
    ⟨binding, found⟩
  have edgeMember : binding.edge ∈ graph.edgeKeys :=
    intake.stepsResolved_of_wellFormed h binding
      (intake.findStep?_sound source binding found).1
  rcases graph.edgeForKey binding.edge edgeMember with ⟨located, edgeFound⟩
  exact ⟨binding, located, found, edgeFound⟩

end AuthoredCFGIntake

end Grass.CFG
