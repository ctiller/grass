import Grass.Platform.Win32.WriteFile
import Grass.Grammar.Endian

/-! Raw synchronous WriteFile results and initialized count-slot observations.
These predicates do not execute a caller read or establish a physical return.
Authority: https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile
-/
namespace Grass.Platform.Win32.WriteFile

open Grass.Core Grass.Memory Grass.Std.Logical

/-- Preserve every BOOL bit. `reportedCount` is a trusted success count only. -/
structure ReturnResult where
  rawBool : BitVec 32
  reportedCount : Option (BitVec 32)
deriving DecidableEq, Repr

/-- Four initialized bytes at the exact argument, using the shared endian view. -/
def DwordAt (memory : MemoryState) (arg : Argument) (count : BitVec 32) : Prop :=
  arg.range.size = 4 ∧ ∀ i : Fin 4,
    memory.cellAt? arg.provenance.root (arg.range.start + i.val) =
      some ((Grass.Grammar.bitVecToLittleEndian (count := 4) count).1.toList[i.val]'(by
        have h := (Grass.Grammar.bitVecToLittleEndian (count := 4) count).2
        change i.val < (Grass.Grammar.bitVecToLittleEndian (count := 4) count).1.length
        rw [h]
        exact i.isLt), true)

/-- `DwordAt.transport` transports observation across allocation equality. -/
theorem DwordAt.transport {before after : MemoryState} {arg : Argument}
    {count : BitVec 32} (observed : DwordAt before arg count)
    (same : after.allocations = before.allocations) : DwordAt after arg count := by
  refine ⟨observed.1, ?_⟩
  intro i
  rw [MemoryState.cellAt?_of_allocations_eq same]
  exact observed.2 i

/-- False exposes no trusted count and constrains neither slot nor accepted prefix.
Nonzero requires the initialized slot to equal the reached accepted count. -/
def ReturnResult.Conforms (result : ReturnResult) (memory : MemoryState)
    (request : Request) (accepted : Nat) : Prop :=
  if result.rawBool = 0 then result.reportedCount = none
  else ∃ count, result.reportedCount = some count ∧ DwordAt memory request.countSlot count ∧
    count.toNat = accepted ∧ count.toNat ≤ request.requested.toNat

/-- `ReturnResult.Conforms.failure` excludes a trusted count on failure. -/
theorem ReturnResult.Conforms.failure {result : ReturnResult} {memory : MemoryState}
    {request : Request} {accepted : Nat} (h : result.Conforms memory request accepted)
    (failed : result.rawBool = 0) : result.reportedCount = none := by
  simpa [ReturnResult.Conforms, failed] using h

/-- Any nonzero BOOL exposes the actual initialized, bounded accepted count. -/
theorem ReturnResult.Conforms.success {result : ReturnResult} {memory : MemoryState}
    {request : Request} {accepted : Nat} (h : result.Conforms memory request accepted)
    (succeeded : result.rawBool ≠ 0) :
    ∃ count, result.reportedCount = some count ∧ DwordAt memory request.countSlot count ∧
      count.toNat = accepted ∧ count.toNat ≤ request.requested.toNat := by
  unfold ReturnResult.Conforms at h
  rw [if_neg succeeded] at h
  exact h

/-- Exact allocation preservation transports success observations and failures. -/
theorem ReturnResult.Conforms.transport {result : ReturnResult} {before after : MemoryState}
    {request : Request} {accepted : Nat} (h : result.Conforms before request accepted)
    (same : after.allocations = before.allocations) : result.Conforms after request accepted := by
  unfold ReturnResult.Conforms at *
  split at h
  · simp_all
  · obtain ⟨count, reported, observed, exactCount, bounded⟩ := h
    split
    · contradiction
    · exact ⟨count, reported, observed.transport same, exactCount, bounded⟩

end Grass.Platform.Win32.WriteFile
