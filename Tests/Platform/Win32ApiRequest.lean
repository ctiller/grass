import Grass.Platform.Win32.ApiRequest
import Grass.Op.CallProtocolCustody
import Tests.Platform.Win32WriteFile

/-! Regression coverage for heterogeneous Win32 pending calls and augmented loans. -/

namespace Grass.Tests.Win32ApiRequest

open Grass.Core Grass.Memory Grass.Op Grass.Op.CallProtocol Grass.Std.Logical
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Tests.Spike1

private def contextSupply : FreshSupply ContextTag := .initial

/-- A third minted context, distinct from the fixture's caller and API agent. -/
def thirdCaller : ContextId := contextSupply.fresh.2.fresh.2.fresh.1

/-- Reuse the fixture machine and register the second caller through the public machine door. -/
def initial : ProtocolState :=
  CallProtocol.initial
    (Grass.Tests.Win32WriteFile.initial.machine.noteContext thirdCaller .thread)
    FreshSupply.initial (by decide)

def stdHandoff :=
  CallProtocol.handoff? initial thirdCaller apiAgent (.getStdHandle 0) []

theorem stdHandoff_exists : stdHandoff.isSome := by decide

def stdCall := (stdHandoff.get stdHandoff_exists).1
def afterStd := (stdHandoff.get stdHandoff_exists).2

/-- An endpoint-specific read loan in unused bytes of the actual owned stack allocation. -/
def additionalLoan : LoanRequest :=
  { kind := .loan
    provenance := stackProvenance
    range := ⟨128, 8⟩
    rights := .readOnly }

def writeLoans := Grass.Tests.Win32WriteFile.request.loans ++ [additionalLoan]

def writeHandoff := CallProtocol.handoff? afterStd mainThread apiAgent
  (.writeFile Grass.Tests.Win32WriteFile.request) writeLoans

theorem writeHandoff_exists : writeHandoff.isSome := by decide

def writeCall := (writeHandoff.get writeHandoff_exists).1
def afterWrite := (writeHandoff.get writeHandoff_exists).2

def stdRecord : CallProtocol.Pending ApiRequest :=
  (afterWrite.pending.lookup stdCall).get (by decide)

def writeApiRecord : CallProtocol.Pending ApiRequest :=
  (afterWrite.pending.lookup writeCall).get (by decide)

def writeRecord : CallProtocol.Pending Grass.Platform.Win32.WriteFile.Request :=
  ((afterWrite.pending.lookup writeCall).bind selectPending).get (by decide)

theorem mixed_pending_entries_retained_and_calls_distinct :
    afterWrite.pending.lookup stdCall = some stdRecord ∧
    afterWrite.pending.lookup writeCall = some writeApiRecord ∧
    stdCall ≠ writeCall := by
  exact ⟨rfl, rfl, by decide⟩

theorem selected_write_record_is_the_exact_embedded_occurrence :
    afterWrite.pending.lookup writeCall = some (embedPending writeRecord) := by rfl

theorem selecting_getStdHandle_yields_none :
    (afterWrite.pending.lookup stdCall).bind selectPending = none := by decide

theorem write_batch_ids_are_distinct : writeApiRecord.ids.Nodup := by decide

private theorem partition :
    writeApiRecord.LoanPartition Grass.Tests.Win32WriteFile.request.loans [additionalLoan] :=
  handoff?_loanPartition (state := afterStd) (next := afterWrite)
    (caller := mainThread) (agent := apiAgent)
    (request := ApiRequest.writeFile Grass.Tests.Win32WriteFile.request)
    (call := writeCall) (by rfl) (by rfl)

theorem actual_batch_is_semantic_then_additional :
    partition.semanticEntries ++ partition.additionalEntries = writeApiRecord.loans :=
  partition.entries_append

theorem actual_batch_has_all_three_ids :
    partition.semanticEntries.length = 2 ∧
    partition.additionalEntries.length = 1 ∧
    writeApiRecord.ids.length = 3 := by decide

theorem semantic_and_additional_grants_are_exact :
    partition.semanticEntries.map Prod.snd =
        Grass.Tests.Win32WriteFile.request.loans.map
          (fun loan => loan.grant mainThread apiAgent) ∧
    partition.additionalEntries.map Prod.snd =
        [additionalLoan.grant mainThread apiAgent] :=
  ⟨partition.semantic_grants, partition.additional_grants⟩

theorem prefix_only_return_is_rejected :
    CallProtocol.return? afterWrite writeCall mainThread apiAgent
      (partition.semanticEntries.map Prod.fst) = none := by decide

def fullReturn := CallProtocol.return? afterWrite writeCall mainThread apiAgent writeApiRecord.ids

theorem fullReturn_exists : fullReturn.isSome := by decide

def returnedRecord := (fullReturn.get fullReturn_exists).1
def afterReturn := (fullReturn.get fullReturn_exists).2

theorem full_return_removes_only_writeFile :
    returnedRecord = writeApiRecord ∧
    afterReturn.pending.lookup writeCall = none ∧
    afterReturn.pending.lookup stdCall = some stdRecord := by
  exact ⟨rfl, by decide, rfl⟩

theorem full_return_preserves_supplies_and_appends_one_boundary :
    afterReturn.callSupply = afterWrite.callSupply ∧
    afterReturn.grantSupply = afterWrite.grantSupply ∧
    afterReturn.boundaries = afterWrite.boundaries ++
      [.returned writeCall mainThread apiAgent writeApiRecord.ids] := by
  exact ⟨rfl, rfl, rfl⟩

end Grass.Tests.Win32ApiRequest
