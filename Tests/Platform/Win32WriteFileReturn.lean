import Grass.Platform.Win32.WriteFileReturn
import Tests.Platform.Win32WriteFile

/-! Return bookkeeping and result-observation fixtures. These use model states
and synthetic raw results; they do not establish a physical ABI return. -/

namespace Grass.Tests.Win32WriteFileReturn

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.WriteFile
open Grass.Tests.Win32WriteFile
open Grass.Tests.Spike1

/-- The existing reached quiet prefix permits exactly the protocol bookkeeping
return for its same pending occurrence and loan identifiers. -/
def returnAttempt :=
  CallProtocol.return? quietState call record.caller record.agent record.ids

example : returnAttempt.isSome := by decide

/-- Zero retains the raw failure bit pattern but provides no trusted count. -/
def failed : ReturnResult := { rawBool := 0, reportedCount := none }

example : failed.Conforms quietState.machine.memory record.request quietPrefix.accepted := by
  simp [ReturnResult.Conforms, failed]

example : ∀ count, failed.reportedCount ≠ some count := by
  intro count equal
  cases equal

/-- Explicitly initialize the four count-slot bytes with a zero DWORD. -/
def zeroDword : BitVec 32 := 0

private def encodedCount : ByteSeq :=
  (Grass.Grammar.bitVecToLittleEndian (count := 4) zeroDword).1.toList

/-- This fixture first prepares the exact count-slot range. It never writes
through an allocation id or substitutes a fallback after failed resolution. -/
private def countAccess? :=
  memory.resolveAccess? request.countSlot.provenance request.countSlot.range

private def countAccess : memory.ResolvedAccess request.countSlot.provenance
    request.countSlot.range :=
  countAccess?.toOption.get (by decide)

theorem count_access_resolves : countAccess? = .ok countAccess := by rfl

private theorem encodedCount_fits : encodedCount.length ≤ request.countSlot.range.size := by
  decide

def initializedMemory : MemoryState :=
  memory.writeResolved countAccess encodedCount true encodedCount_fits

theorem initialized_zero_dword : DwordAt initializedMemory request.countSlot zeroDword := by
  constructor
  · rfl
  · intro i
    change initializedMemory.cellAt? request.countSlot.provenance.root
      (request.countSlot.range.start + i.val) = _
    rw [show initializedMemory = memory.writeResolved countAccess encodedCount true encodedCount_fits
      by rfl]
    rw [MemoryState.cellAt?_writeResolved_of_covers memory countAccess encodedCount true
      encodedCount_fits (by
        change 16 ≤ 16 + i.val ∧ 16 + i.val < 16 + encodedCount.length
        have hlength : encodedCount.length = 4 := by decide
        rw [hlength]
        omega)]
    simp [encodedCount]

/-- BOOL `2` is a success, not only BOOL `1`; it trusts an explicitly
initialized synthetic zero count for a zero-accepted observation. -/
def nonOneSuccess : ReturnResult := { rawBool := 2, reportedCount := some zeroDword }

example : nonOneSuccess.Conforms initializedMemory request 0 := by
  refine ⟨zeroDword, rfl, initialized_zero_dword, rfl, by decide⟩

/-- A reported one cannot stand for a reached accepted count of zero. -/
def wrongCount : ReturnResult := { rawBool := 2, reportedCount := some 1 }

example : ¬ wrongCount.Conforms initializedMemory request 0 := by
  intro conforms
  obtain ⟨count, reported, _, accepted, _⟩ :=
    conforms.success (by decide : wrongCount.rawBool ≠ 0)
  rw [show wrongCount.reportedCount = some 1 by rfl] at reported
  cases Option.some.inj reported
  simp at accepted

/-- The same nonzero raw BOOL is refused if its count-slot bytes were never
initialized; no caller read or physical return is implied by this test. -/
example : ¬ nonOneSuccess.Conforms memory request 0 := by
  intro conforms
  obtain ⟨count, reported, observed, _, _⟩ :=
    conforms.success (by decide : nonOneSuccess.rawBool ≠ 0)
  rw [show nonOneSuccess.reportedCount = some zeroDword by rfl] at reported
  cases Option.some.inj reported
  have first := observed.2 ⟨0, by decide⟩
  change memory.cellAt? stackAlloc 16 = _ at first
  have absent : memory.cellAt? stackAlloc 16 = none := by decide
  rw [absent] at first
  contradiction

end Grass.Tests.Win32WriteFileReturn
