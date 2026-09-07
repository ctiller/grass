import Grass.CFG.Manifest
import Tests.CFG.Compose

/-!
# CFG manifest fixtures

The diamond fixture pins exact blocks, edges, joins, calls, and stack assignments
derived from one structurally closed composition.
-/

namespace Grass.Tests.CFG.Manifest

open Grass.CFG
open Grass.Tests.CFG.Compose

def closed : ClosedManifest graph where
  composition := withCall
  closed := by native_decide

example : closed.manifest.blocks = graph.blockIds := rfl
example : closed.manifest.edges = graph.manifestEdges := rfl
example : closed.manifest.joins = graph.discoverJoins := rfl
example : closed.manifest.loops = graph.discoverLoops := rfl
example : closed.manifest.blockStacks = stacks.blocks := rfl
example : closed.manifest.edgeStacks = stacks.edges := rfl

example : closed.manifest.calls = [{
    block := blockId "entry"
    target := .local (blockId "left")
    outcomes := [⟨exitTag "normal", .normal⟩]
    returns := [⟨exitTag "normal", .block (blockId "join")⟩]
  }] := by native_decide

example : closed.manifest.edges = [
    ⟨blockId "entry", exitTag "left", .block (blockId "left")⟩,
    ⟨blockId "entry", exitTag "right", .block (blockId "right")⟩,
    ⟨blockId "left", exitTag "next", .block (blockId "join")⟩,
    ⟨blockId "right", exitTag "next", .block (blockId "join")⟩,
    ⟨blockId "join", exitTag "return", .terminal .returned⟩
  ] := by native_decide

end Grass.Tests.CFG.Manifest
