import Grass.Platform.Win32.WriteFileReturn

/-! Finite, explicitly synthetic provider selection for one complete WriteFile.
The Hello consumer selects these exact action/endpoints once for its whole raw
run. These predicates do not execute an action, establish memory ordering, or
assert native dispatch/publication. Actual checked execution, causal evidence,
count bytes, and the enclosing history remain consumer obligations. -/

namespace Grass.Tests.Win32WriteFileProviderModel

open Grass.Core Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.WriteFile

/-- One selected action at one exact call and pair of protocol endpoints. -/
def selectedAction (call : CallProtocol.CallId) (record : CallProtocol.Pending Request)
    (action : Action) (before after : ProtocolState)
    (candidateCall : CallProtocol.CallId) (candidateRecord : CallProtocol.Pending Request)
    (candidateAction : Action) (candidateBefore candidateAfter : ProtocolState) : Prop :=
  candidateCall = call ∧ candidateRecord = record ∧ candidateAction = action ∧
    candidateBefore = before ∧ candidateAfter = after

/-- The fixed model permits only the selected full-publication observation.
`CommittedStep` must still supply actual execution and the observed prefix. -/
def realization (causal : CausalModel) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) (action : Action) (before after : ProtocolState) :
    Realization where
  causal := causal
  executesFor := selectedAction call record action before after
  publishes := fun candidateCall candidateRecord candidateAction candidateBefore candidateAfter
      acceptedBefore acceptedAfter output =>
    selectedAction call record action before after candidateCall candidateRecord candidateAction
      candidateBefore candidateAfter ∧
      acceptedBefore = 0 ∧ acceptedAfter = record.request.requested.toNat ∧
      output = record.request.bytes

/-- BOOL two deliberately retains a non-one success pattern. The checked
`MatchedReturn.conforms` premise must establish the actual initialized DWORD. -/
def result (record : CallProtocol.Pending Request) : ReturnResult :=
  ⟨2, some record.request.requested⟩

/-- Select exactly one return at the fixed model's service endpoint. This is
fixture data, not native result correspondence or evidence that return ran. -/
def interpretation (fixed : Realization) (call : CallProtocol.CallId)
    (record : CallProtocol.Pending Request) (before after : ProtocolState) : ReturnInterpretation :=
  fun candidateRealization candidateCall candidateRecord candidateBefore candidateAfter accepted raw =>
    candidateRealization = fixed ∧ candidateCall = call ∧ candidateRecord = record ∧
      candidateBefore = before ∧ candidateAfter = after ∧
      accepted = record.request.requested.toNat ∧ raw = result record

theorem result_raw_bool (record : CallProtocol.Pending Request) :
    (result record).rawBool = 2 := rfl

theorem publication_exact {causal : CausalModel} {call : CallProtocol.CallId}
    {record : CallProtocol.Pending Request} {action : Action} {before after : ProtocolState}
    {candidateCall : CallProtocol.CallId} {candidateRecord : CallProtocol.Pending Request}
    {candidateAction : Action} {candidateBefore candidateAfter : ProtocolState}
    {acceptedBefore acceptedAfter : Nat} {output : Vec Byte}
    (published : (realization causal call record action before after).publishes
      candidateCall candidateRecord candidateAction candidateBefore candidateAfter
      acceptedBefore acceptedAfter output) :
    candidateCall = call ∧ candidateRecord = record ∧ candidateAction = action ∧
      candidateBefore = before ∧ candidateAfter = after ∧ acceptedBefore = 0 ∧
      acceptedAfter = record.request.requested.toNat ∧ output = record.request.bytes :=
  ⟨published.1.1, published.1.2.1, published.1.2.2.1, published.1.2.2.2.1,
    published.1.2.2.2.2, published.2.1, published.2.2.1, published.2.2.2⟩

end Grass.Tests.Win32WriteFileProviderModel
