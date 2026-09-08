import Grass.Build.Manifest.Rooted
import Tests.Build.Manifest.Dag

/-! # Rooted manifest DAG fixtures -/

namespace Grass.Tests.Build.Manifest

open Grass.Build.Manifest Grass.Std.Logical

example : fixtureDag.Rooted := by decide
example : diamondDag.Rooted := by decide
example : (checkRootedManifestDag fixtureDag).isSome = true := by decide

/-- Two valid ordered nodes with no connecting edge form a forest, not the
single rooted hierarchy required by final artifact composition. -/
def disconnectedDag : ManifestDag 2 where
  nodes := Vec.fromList [node leafA Vec.empty, node leafB Vec.empty]

example : disconnectedDag.WellFormed := by decide
example : ¬disconnectedDag.Rooted := by decide
example : checkRootedManifestDag disconnectedDag = none := by decide

def emptyDag : ManifestDag 2 := ⟨Vec.empty⟩

example : emptyDag.WellFormed := by decide
example : ¬emptyDag.Rooted := by decide
example : checkRootedManifestDag emptyDag = none := by decide

example (dag : RootedManifestDag 2) :
    dag.graph.WellFormed ∧ dag.graph.nodes.length ≠ 0 ∧
      NodesFeedLater dag.graph.nodes.toList := by
  exact ⟨dag.wellFormed, dag.nonempty, dag.feedsLater⟩

end Grass.Tests.Build.Manifest
