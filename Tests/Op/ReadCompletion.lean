import Grass.Op.ReadCompletion
import Tests.Op.FakeIsa

/-! Focused uses of the generic read-completion bridge against FakeIsa's
initialized eight-byte load. -/

namespace Tests.Op.ReadCompletion

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Tests.FakeIsa

def loadDescriptor : AccessDescriptor :=
  acc bufferProv ⟨0, 8⟩ 0x1000 .read .readWrite true false

example : ∃ resolved : state₀.memory.ResolvedAccess
    loadDescriptor.provenance loadDescriptor.range,
    prepareAccess state₀.memory loadDescriptor = .ok resolved := by
  refine ⟨_, rfl⟩

example : ∃ (resolved : state₀.memory.ResolvedAccess
      loadDescriptor.provenance loadDescriptor.range)
    (complete : CompleteCommitted loadDescriptor),
    prepareAccess state₀.memory loadDescriptor = .ok resolved ∧
    (Oracle.ofMemory storedBytes indeterminateByte).answerResolved
      state₀ loadDescriptor resolved = some complete := by
  refine ⟨_, _, rfl, rfl⟩

/-- Preparation certifies the initialized range, which in turn makes two
deliberately different indeterminate providers observationally identical. -/
theorem initialized_load_ignores_indeterminate
    (resolved : state₀.memory.ResolvedAccess loadDescriptor.provenance loadDescriptor.range)
    (prepared : prepareAccess state₀.memory loadDescriptor = .ok resolved) :
    resolved.RangeInitialized ∧
    observedBytes resolved (fun _ => 0x11) = observedBytes resolved (fun _ => 0xEE) := by
  have initialized := rangeInitialized_of_prepareAccess_allBytesInitialized prepared rfl
  exact ⟨initialized,
    observedBytes_eq_of_rangeInitialized resolved initialized (fun _ => 0x11) (fun _ => 0xEE)⟩

private def emptyBackings : Option MemoryState :=
  allocations₀.foldlM (fun state entry =>
    state.installBacking? entry.2.backing
      ⟨entry.2.extent.stop + entry.2.origin, ByteStore.empty⟩) MemoryState.empty

private def emptyMemorySetup : Option MemoryState :=
  emptyBackings.bind (fun state => state.allocateAll? allocations₀)

private def emptyMemory : MemoryState := emptyMemorySetup.getD .empty

private def permissiveLoad : AccessDescriptor :=
  { loadDescriptor with
    initialization := .permitsUninitialized ⟨"read-completion.fixture"⟩ }

/-- The guard is discriminating: with the same allocation layout but missing
backing cells, two fallback providers produce different observed bytes. -/
example : ∃ resolved : emptyMemory.ResolvedAccess permissiveLoad.provenance permissiveLoad.range,
    prepareAccess emptyMemory permissiveLoad = .ok resolved ∧
    observedBytes resolved (fun _ => 0x11) ≠ observedBytes resolved (fun _ => 0xEE) := by
  refine ⟨_, rfl, ?_⟩
  decide

/-- The FakeIsa memory oracle's answer is connected to the exact resolved
backing observation, rather than merely to an arbitrary full-width byte list. -/
theorem memory_oracle_answer_observes_resolved
    (resolved : state₀.memory.ResolvedAccess loadDescriptor.provenance loadDescriptor.range)
    (complete : CompleteCommitted loadDescriptor)
    (answer : (Oracle.ofMemory storedBytes indeterminateByte).answerResolved
      state₀ loadDescriptor resolved = some complete) :
    complete.committed.observed =
      some (observedBytes resolved (indeterminateByte state₀ loadDescriptor)) :=
  Oracle.ofMemory_observed_of_answerResolved storedBytes indeterminateByte state₀
    loadDescriptor resolved complete answer rfl

/-- Performing the completed FakeIsa load frames both storage tables. -/
theorem completed_load_frames_storage
    (resolved : state₀.memory.ResolvedAccess loadDescriptor.provenance loadDescriptor.range)
    (prepared : prepareAccess state₀.memory loadDescriptor = .ok resolved)
    (complete : CompleteCommitted loadDescriptor) :
    let after := performPreparedAccess policy state₀ loadDescriptor resolved prepared
      (.completed complete) .thread ⟨⟨"read-completion.fixture"⟩⟩
    after.memory.allocations = state₀.memory.allocations ∧
      after.memory.backings = state₀.memory.backings := by
  exact performPreparedAccess_readOnly_storage policy state₀ loadDescriptor resolved
    prepared (.completed complete) .thread ⟨⟨"read-completion.fixture"⟩⟩ rfl

end Tests.Op.ReadCompletion
