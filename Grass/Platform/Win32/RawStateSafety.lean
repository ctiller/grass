import Grass.Platform.Win32.RawSafety

/-! Fixed state and fault-vocabulary obligations for the current single-caller
Windows raw domain. These are proof requirements, not a theorem that every
LoadedImage satisfies them. They retain archived obligations and faults and do
not claim a race-freedom or native-adequacy theorem. -/

namespace Grass.Platform.Win32.Raw

open Grass.Core Grass.Memory Grass.Op
open Grass.Platform.Win32.ExecutionState Grass.Platform.Win32.Loader

/-- Selected spatial-profile, violation-ledger and call-bookkeeping invariants.
PlacementValid includes dedicated backing storage; ControlConsistent includes
successful repacking of the exact protocol metadata against this machine. -/
structure StateSafety (state : RawState) : Prop where
  violations : state.machine.machine.violations.IsEmpty
  placement : Loader.PlacementValid state.machine.machine.memory
  control : state.ControlConsistent
  runtime : state.RuntimeLinked

variable {image : ImageInput} {inputs : EntryInputs}
  {loaded : LoadedImage image inputs} {realization : WriteFile.Realization}
  {environment : ConsoleEnvironment} {interpretation : WriteFile.ReturnInterpretation}
  {covered : CallProtocol.GrantSupplyCovers loaded.initialState.machine.memory
    (FreshSupply.initial : FreshSupply GrantTag)}

/-- The actual loader root must satisfy the same fixed invariants as later
prefixes. LoadedImage alone does not imply a clean violation ledger. -/
def InitialAdmission : Prop := StateSafety (initialState loaded covered)

/-- Every newly recorded fault class is recognized by the actual producing
policy's vocabulary. This is registry coverage; the actual RawStep retains
the operation and fault-production evidence.
Existing incoming faults are retained as archive, not reclassified as faults
produced by this program. Endpoint bookkeeping edges introduce no new faults. -/
def FaultSuffixRecognized (before after : RawState) (choice : Choice) : Prop :=
  match choice with
  | .cpu _ => ∃ policy, Cpu.policy? loaded before.machine = some policy ∧
      ∃ added, after.machine.machine.faults = before.machine.machine.faults ++ added ∧
        ∀ raised ∈ added, policy.operationPolicy.profile.vocabulary.faultClasses.Recognizes raised.fault
  | .providerService _ _ action =>
      ∃ added, after.machine.machine.faults = before.machine.machine.faults ++ added ∧
        ∀ raised ∈ added, action.policy.profile.vocabulary.faultClasses.Recognizes raised.fault
  | .apiEntry _ _ | .providerReturn _ _ _ _ | .stdoutResult _ _ _ | .exitObservation _ _ =>
      after.machine.machine.faults = before.machine.machine.faults

/-- Every actual initialized prefix satisfies the fixed state invariants, and
every actual next edge recognizes its fault suffix in its own policy vocabulary.
Coverage and finite/complete progress remain separate mandatory obligations. -/
structure HistorySafety : Prop where
  states : ∀ history : (system loaded realization environment interpretation covered).History,
    StateSafety history.state.down
  faults : ∀ (history : (system loaded realization environment interpretation covered).History)
    {next : ULift.{1} RawState} {nextGraph : ULift.{1} Graph}
    (choice : Choice) (event : ULift.{1} Event),
    (system loaded realization environment interpretation covered).Step
      history.graph history.state choice event next nextGraph →
    FaultSuffixRecognized (loaded := loaded) history.state.down next.down choice

/-- All-history safety includes the actual zero-step loader root. -/
theorem HistorySafety.initial
    (safe : HistorySafety (loaded := loaded) (realization := realization)
      (environment := environment) (interpretation := interpretation) (covered := covered)) :
    InitialAdmission (loaded := loaded) (covered := covered) :=
  safe.states (Grass.RelationalSystem.History.initial
    (state := ⟨initialState loaded covered⟩) (graph := ⟨[]⟩) ⟨rfl, rfl⟩)

end Grass.Platform.Win32.Raw
