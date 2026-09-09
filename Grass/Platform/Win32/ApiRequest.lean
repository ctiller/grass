import Grass.Platform.Win32.WriteFileArguments

namespace Grass.Platform.Win32

open Grass.Op

inductive ApiRequest where
  | getStdHandle (selector : BitVec 32)
  | writeFile (request : WriteFile.Request)
  | exitProcess (status : BitVec 32)

namespace WriteFile

/-- Provider execution retains the entire heterogeneous Windows call table. -/
abbrev ProtocolState := CallProtocol.State ApiRequest

/-- Embed one pending WriteFile occurrence while retaining its recorded custody. -/
def embedPending (record : CallProtocol.Pending Request) : CallProtocol.Pending ApiRequest where
  caller := record.caller
  agent := record.agent
  request := .writeFile record.request
  loans := record.loans

/-- Select a pending WriteFile occurrence without inspecting or rebuilding its loans. -/
def selectPending (record : CallProtocol.Pending ApiRequest) : Option (CallProtocol.Pending Request) :=
  match record.request with
  | .writeFile request => some {
      caller := record.caller
      agent := record.agent
      request := request
      loans := record.loans }
  | _ => none

theorem embedPending_injective : Function.Injective embedPending := by
  intro left right same
  cases left
  cases right
  simp only [embedPending] at same
  injection same with caller agent request loans
  cases caller
  cases agent
  cases request
  cases loans
  rfl

@[simp] theorem selectPending_embedPending (record : CallProtocol.Pending Request) :
    selectPending (embedPending record) = some record := by
  cases record
  rfl

theorem embedPending_of_selectPending_eq_some
    {actual : CallProtocol.Pending ApiRequest} {record : CallProtocol.Pending Request}
    (selected : selectPending actual = some record) : embedPending record = actual := by
  cases actual with
  | mk caller agent request loans =>
      cases request <;> simp [selectPending] at selected
      case writeFile request =>
        cases selected
        rfl

@[simp] theorem embedPending_ids (record : CallProtocol.Pending Request) :
    (embedPending record).ids = record.ids := rfl

theorem embedPending_valid {record : CallProtocol.Pending Request} {memory : Grass.Memory.MemoryState} :
    (embedPending record).Valid memory ↔ record.Valid memory := by
  rfl

end WriteFile

end Grass.Platform.Win32
