import Grass.Platform.Win32.RawStep

/-!
# Fixed model-only WriteFile causal schedule

The caller selects one explicit finite schedule for a whole model trace. Only
listed nodes receive ranks; an omitted node creates no edge. This fixture gives
the schedule no native timing, dispatch, publication, or memory meaning.
-/

namespace Grass.Tests.Win32WriteFileCausalSchedule

open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile

def rank? (schedule : List CausalNode) (node : CausalNode) : Option Nat :=
  schedule.idxOf? node

def before? (schedule : List CausalNode) (left right : CausalNode) : Bool :=
  match rank? schedule left, rank? schedule right with
  | some i, some j => i < j
  | _, _ => false

/-- Activate only the nodes represented at one trace frontier, while retaining
their ranks from the unchanged whole-trace schedule. -/
def activeGraph (schedule active : List CausalNode) : Raw.Graph :=
  active.flatMap fun left =>
    active.filterMap fun right =>
      if before? schedule left right then some (left, right) else none

def graph (schedule : List CausalNode) : Raw.Graph := activeGraph schedule schedule

/-- Preserve an already established graph prefix and append the newly active
fixed-schedule edges. Consumers separately prove the combined graph realizes
their current represented logs. -/
def extendGraph (prior : Raw.Graph) (schedule active : List CausalNode) : Raw.Graph :=
  prior ++ activeGraph schedule active

theorem extendGraph_extends (prior : Raw.Graph) (schedule active : List CausalNode) :
    prior.Extends (extendGraph prior schedule active) :=
  ⟨activeGraph schedule active, rfl⟩

def model (schedule : List CausalNode) : CausalModel where
  precedes state left right :=
    left ∈ schedule ∧ right ∈ schedule ∧
      Represented state left ∧ Represented state right ∧ before? schedule left right = true

theorem before_irrefl (schedule : List CausalNode) (node : CausalNode) :
    before? schedule node node = false := by
  cases found : schedule.idxOf? node <;> simp [before?, rank?, found]

theorem before_trans {schedule : List CausalNode} {a b c : CausalNode}
    (ab : before? schedule a b = true) (bc : before? schedule b c = true) :
    before? schedule a c = true := by
  unfold before? rank? at *
  split at ab <;> split at bc <;> split <;> simp_all <;> omega

theorem activeGraph_mem_iff {schedule active : List CausalNode} {a b : CausalNode} :
    (a, b) ∈ activeGraph schedule active ↔
      a ∈ active ∧ b ∈ active ∧ before? schedule a b = true := by
  simp [activeGraph]
  constructor
  · rintro ⟨left, leftMem, right, rightMem, ordered, rfl, rfl⟩
    exact ⟨leftMem, rightMem, ordered⟩
  · rintro ⟨leftMem, rightMem, ordered⟩
    exact ⟨a, leftMem, b, rightMem, ordered, rfl, rfl⟩

theorem ordered_path_implies_before {schedule : List CausalNode} {edges : Raw.Graph}
    (edgeOrdered : ∀ left right, (left, right) ∈ edges →
      before? schedule left right = true) {a b : CausalNode}
    (path : Relation.TransGen (fun left right => (left, right) ∈ edges) a b) :
    before? schedule a b = true := by
  induction path with
  | single edge => exact edgeOrdered _ _ edge
  | tail path edge ih => exact before_trans ih (edgeOrdered _ _ edge)

theorem relation_path_implies_before {schedule active : List CausalNode} {a b : CausalNode}
    (path : Relation.TransGen
      (fun left right => (left, right) ∈ activeGraph schedule active) a b) :
    before? schedule a b = true :=
  ordered_path_implies_before
    (fun _ _ edge => (activeGraph_mem_iff.mp edge).2.2) path

theorem valid (schedule : List CausalNode) (state : ProtocolState) :
    (model schedule).Valid state where
  endpoints := by intro a b ordered; exact ⟨ordered.2.2.1, ordered.2.2.2.1⟩
  irreflexive := by
    intro node ordered
    have impossible := ordered.2.2.2.2
    rw [before_irrefl] at impossible
    contradiction
  transitive := by
    intro a b c ab bc
    exact ⟨ab.1, bc.2.1, ab.2.2.1, bc.2.2.2.1,
      before_trans ab.2.2.2.2 bc.2.2.2.2⟩

/-- If every selected node is actually represented, the computed graph and
the fixed model are exactly the same strict order. -/
theorem realizes (schedule active : List CausalNode) (state : ProtocolState)
    (coverage : ∀ node, node ∈ active ↔ node ∈ schedule ∧ Represented state node) :
    (activeGraph schedule active).Realizes (model schedule) state := by
  intro left right
  constructor
  · intro ordered
    exact Relation.TransGen.single
      (activeGraph_mem_iff.mpr
        ⟨(coverage left).2 ⟨ordered.1, ordered.2.2.1⟩,
          (coverage right).2 ⟨ordered.2.1, ordered.2.2.2.1⟩, ordered.2.2.2.2⟩)
  · intro path
    have ordered := relation_path_implies_before path
    have ends : left ∈ active ∧ right ∈ active := by
      clear ordered
      induction path with
      | single edge =>
          exact ⟨(activeGraph_mem_iff.mp edge).1, (activeGraph_mem_iff.mp edge).2.1⟩
      | tail path edge ih => exact ⟨ih.1, (activeGraph_mem_iff.mp edge).2.1⟩
    have leftFacts := (coverage left).1 ends.1
    have rightFacts := (coverage right).1 ends.2
    exact ⟨leftFacts.1, rightFacts.1, leftFacts.2, rightFacts.2, ordered⟩

theorem wellFormed (schedule active : List CausalNode) (state : ExecutionState.RawState)
    (represented : ∀ node ∈ active, Raw.Represented state node) :
    (activeGraph schedule active).WellFormed state := by
  constructor
  · intro edge member
    have facts := activeGraph_mem_iff.mp member
    exact ⟨represented edge.1 facts.1, represented edge.2 facts.2.1⟩
  · intro node cycle
    have ordered := relation_path_implies_before cycle
    rw [before_irrefl] at ordered
    contradiction

/-- Appending the complete active graph realizes the current model when every
old edge remains a current model edge. -/
theorem extendGraph_realizes (prior : Raw.Graph) (schedule active : List CausalNode)
    (state : ProtocolState)
    (coverage : ∀ node, node ∈ active ↔ node ∈ schedule ∧ Represented state node)
    (priorSound : ∀ left right, (left, right) ∈ prior →
      (model schedule).precedes state left right) :
    (extendGraph prior schedule active).Realizes (model schedule) state := by
  let edgeSound : ∀ left right, (left, right) ∈ extendGraph prior schedule active →
      (model schedule).precedes state left right := by
    intro left right member
    change (left, right) ∈ prior ++ activeGraph schedule active at member
    rw [List.mem_append] at member
    cases member with
    | inl old => exact priorSound left right old
    | inr fresh =>
        have facts := activeGraph_mem_iff.mp fresh
        have leftFacts := (coverage left).1 facts.1
        have rightFacts := (coverage right).1 facts.2.1
        exact ⟨leftFacts.1, rightFacts.1, leftFacts.2, rightFacts.2, facts.2.2⟩
  intro left right
  constructor
  · intro ordered
    apply Relation.TransGen.single
    rw [extendGraph, List.mem_append]
    exact Or.inr (activeGraph_mem_iff.mpr
      ⟨(coverage left).2 ⟨ordered.1, ordered.2.2.1⟩,
        (coverage right).2 ⟨ordered.2.1, ordered.2.2.2.1⟩, ordered.2.2.2.2⟩)
  · intro path
    have ordered := ordered_path_implies_before
      (fun a b edge => (edgeSound a b edge).2.2.2.2) path
    have endpoints : Represented state left ∧ Represented state right := by
      clear ordered
      induction path with
      | single edge =>
          exact ⟨(edgeSound _ _ edge).2.2.1, (edgeSound _ _ edge).2.2.2.1⟩
      | tail path edge ih => exact ⟨ih.1, (edgeSound _ _ edge).2.2.2.1⟩
    have scheduled : left ∈ schedule ∧ right ∈ schedule := by
      clear ordered endpoints
      induction path with
      | single edge => exact ⟨(edgeSound _ _ edge).1, (edgeSound _ _ edge).2.1⟩
      | tail path edge ih => exact ⟨ih.1, (edgeSound _ _ edge).2.1⟩
    exact ⟨scheduled.1, scheduled.2, endpoints.1, endpoints.2, ordered⟩

/-- Old endpoints plus one fixed rank order are sufficient for the appended
active graph to remain acyclic and log-represented. -/
theorem extendGraph_wellFormed (prior : Raw.Graph) (schedule active : List CausalNode)
    (state : ExecutionState.RawState)
    (priorEndpoints : prior.Endpoints state)
    (priorOrdered : ∀ left right, (left, right) ∈ prior →
      before? schedule left right = true)
    (represented : ∀ node ∈ active, Raw.Represented state node) :
    (extendGraph prior schedule active).WellFormed state := by
  constructor
  · intro edge member
    rw [extendGraph, List.mem_append] at member
    cases member with
    | inl old => exact priorEndpoints edge old
    | inr fresh =>
        have facts := activeGraph_mem_iff.mp fresh
        exact ⟨represented edge.1 facts.1, represented edge.2 facts.2.1⟩
  · intro node cycle
    have ordered := ordered_path_implies_before (edges := extendGraph prior schedule active)
      (by
        intro left right member
        rw [extendGraph, List.mem_append] at member
        cases member with
        | inl old => exact priorOrdered left right old
        | inr fresh => exact (activeGraph_mem_iff.mp fresh).2.2)
      cycle
    rw [before_irrefl] at ordered
    contradiction

private def calls : Grass.Core.FreshSupply Grass.Op.CallProtocol.CallTag := .initial
private def first := calls.fresh.1
private def second := calls.fresh.2.fresh.1
private def sample : List CausalNode := [.entry first, .returned first]
private def entryOnly : List CausalNode := [.entry first]

example : before? sample (.entry first) (.returned first) = true := by decide
example : (before? sample (.returned first) (.entry first)) = false := by decide
example : (before? sample (.entry second) (.returned first)) = false := by decide
example : ((.entry first, .returned first) ∈ graph sample) := by decide
example : ¬ ((.returned first, .entry first) ∈ graph sample) := by decide
example : activeGraph sample entryOnly = [] := by decide
example : ¬ ((.entry first, .returned first) ∈ activeGraph sample entryOnly) := by decide
example : ∀ node, ¬ Relation.TransGen
    (fun left right => (left, right) ∈ graph sample) node node := by
  intro node cycle
  have ordered := relation_path_implies_before cycle
  rw [before_irrefl] at ordered
  contradiction

end Grass.Tests.Win32WriteFileCausalSchedule
