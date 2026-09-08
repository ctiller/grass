import Grass.Build.Manifest.Dag

/-!
# Rooted manifest dependency DAGs

`RootedManifestDag` strengthens ordered graph admission with a nonempty single-
root hierarchy: every node except the final root feeds at least one later parent.
The recursive condition permits shared children while rejecting disconnected
manifest components.
-/

namespace Grass.Build.Manifest

open Grass.Std.Logical

/-- Executable check that each nonfinal node is a child of a later node. -/
def nodesFeedLater {fanout : Nat} : List (DependencyNode fanout) → Bool
  | [] => true
  | [_] => true
  | node :: next :: rest =>
      (next :: rest).any (fun parent => parent.dependencies.contains node.scope) &&
        nodesFeedLater (next :: rest)

/-- Propositional hierarchy condition corresponding to `nodesFeedLater`. -/
def NodesFeedLater {fanout : Nat} : List (DependencyNode fanout) → Prop
  | [] => True
  | [_] => True
  | node :: next :: rest =>
      (∃ parent ∈ next :: rest, node.scope ∈ parent.dependencies) ∧
        NodesFeedLater (next :: rest)

/-- `nodesFeedLater_eq_true_iff` connects the executable hierarchy check to its
exact direct-parent witnesses. -/
theorem nodesFeedLater_eq_true_iff {fanout : Nat}
    (nodes : List (DependencyNode fanout)) :
    nodesFeedLater nodes = true ↔ NodesFeedLater nodes := by
  induction nodes with
  | nil => simp [nodesFeedLater, NodesFeedLater]
  | cons node rest inductionHypothesis =>
      cases rest with
      | nil => simp [nodesFeedLater, NodesFeedLater]
      | cons next tail =>
          simp [nodesFeedLater, NodesFeedLater, Vec.contains_iff_mem,
            inductionHypothesis]

/-- A rooted manifest is a well-formed nonempty DAG whose nonfinal nodes feed
later parents. -/
def ManifestDag.Rooted {fanout : Nat} (dag : ManifestDag fanout) : Prop :=
  dag.WellFormed ∧ dag.nodes.length ≠ 0 ∧
    nodesFeedLater dag.nodes.toList = true

instance ManifestDag.instDecidableRooted {fanout : Nat}
    (dag : ManifestDag fanout) : Decidable dag.Rooted := by
  unfold Rooted
  infer_instance

/-- Generated manifest metadata admitted as one connected rooted hierarchy. -/
structure RootedManifestDag (fanout : Nat) where
  graph : ManifestDag fanout
  rooted : graph.Rooted

/-- Validate graph ordering, uniqueness, nonemptiness, and root connectivity. -/
def checkRootedManifestDag {fanout : Nat} (dag : ManifestDag fanout) :
    Option (RootedManifestDag fanout) :=
  if rooted : dag.Rooted then some ⟨dag, rooted⟩ else none

/-- `checkRootedManifestDag_isSome_iff` exactly characterizes rooted admission. -/
theorem checkRootedManifestDag_isSome_iff {fanout : Nat}
    (dag : ManifestDag fanout) :
    (checkRootedManifestDag dag).isSome = true ↔ dag.Rooted := by
  simp [checkRootedManifestDag]

/-- Rooted admission includes ordinary graph well-formedness. -/
theorem RootedManifestDag.wellFormed {fanout : Nat}
    (dag : RootedManifestDag fanout) : dag.graph.WellFormed :=
  dag.rooted.1

/-- Rooted admission excludes an empty manifest graph. -/
theorem RootedManifestDag.nonempty {fanout : Nat}
    (dag : RootedManifestDag fanout) : dag.graph.nodes.length ≠ 0 :=
  dag.rooted.2.1

/-- Rooted admission retains the exact recursive parent-connectivity witnesses. -/
theorem RootedManifestDag.feedsLater {fanout : Nat}
    (dag : RootedManifestDag fanout) : NodesFeedLater dag.graph.nodes.toList :=
  (nodesFeedLater_eq_true_iff dag.graph.nodes.toList).mp dag.rooted.2.2

end Grass.Build.Manifest
