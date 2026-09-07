import Grass.Certificate

/-!
# VerifiedProgram composition

The public gate contains only stratified certificates. Soundness is derived by
composing adjacent relational simulations, and emitted bytes are derived from
the exact certified artifact through its selected canonical writer.
-/

namespace Grass

variable {spec : SpecProcess}

/-- The sole certificate accepted by verified emission. -/
structure VerifiedProgram (spec : SpecProcess) where
  portable : PortableProgramCertificate spec
  driver : ProjectedDriverCertificate portable
  provider : ProviderCertificate driver
  machine : MachineCertificate provider
  artifact : ArtifactCertificate machine

/-- Verified emission invokes the writer selected by the artifact certificate. -/
def emitProgram (verified : VerifiedProgram spec) : ByteArray :=
  verified.artifact.format.write verified.artifact.artifact

namespace VerifiedProgram

/-- Emission is byte-for-byte the selected machine profile's encoding of the
exact raw instructions elaborated from the selected authored source. -/
theorem emitProgram_eq_encodedBytes (verified : VerifiedProgram spec) :
    emitProgram verified = verified.machine.encodedBytes :=
  verified.artifact.representationExact

/-- Decoding verified emission under its selected profile recovers exactly the
raw instruction list elaborated from its selected authored source. -/
theorem decode_emitProgram (verified : VerifiedProgram spec) :
    verified.machine.code.decode verified.machine.profile
        (emitProgram verified) =
      some verified.machine.instructions := by
  rw [verified.emitProgram_eq_encodedBytes]
  exact verified.machine.decode_encodedBytes

/-- Parsing the emitted bytes selects the exact certified artifact behavior. -/
theorem loadedBehavior_exact (verified : VerifiedProgram spec) :
    verified.artifact.format.loadedBehavior (emitProgram verified) =
      verified.artifact.format.artifactBehavior verified.artifact.artifact :=
  verified.artifact.format.loadExact
    (verified.artifact.format.writeParses verified.artifact.artifact)

/-- Loading verified emission yields exactly the selected target semantics of
the decoded source expansion, not an independently authored lookalike. -/
theorem loadedMachineBehavior_exact (verified : VerifiedProgram spec) :
    verified.artifact.format.loadedBehavior (emitProgram verified) =
      verified.machine.behavior :=
  verified.artifact.loadedBehaviorExact

/-- The behavior loaded from exact emitted bytes refines the selected target
semantics of the exact authored-source expansion. Together with
`VerifiedProgram.emitProgram_eq_encodedBytes`, this is the public connection
from source through encoding and artifact loading to target behavior. -/
def emittedMachineRefinement (verified : VerifiedProgram spec) :
    BehaviorRefinement
      (verified.artifact.format.loadedBehavior (emitProgram verified))
      verified.machine.behavior :=
  BehaviorRefinement.castConcrete verified.loadedMachineBehavior_exact
    (BehaviorRefinement.refl verified.machine.behavior)

/-- The exact behavior loaded from emitted bytes inherits the artifact
certificate's paired execution and completion adequacy guarantee. -/
theorem loadedAdequate (verified : VerifiedProgram spec) :
    (verified.artifact.format.loadedBehavior (emitProgram verified)).Adequate :=
  ProgramBehavior.Adequate.cast verified.loadedBehavior_exact
    verified.artifact.adequate

/-- Loaded artifact behavior refines the portable process behavior. -/
def refinement (verified : VerifiedProgram spec) :
    BehaviorRefinement
      (verified.artifact.format.loadedBehavior (emitProgram verified))
      verified.portable.behavior :=
  BehaviorRefinement.castConcrete verified.loadedBehavior_exact
    (((verified.artifact.refinement.trans verified.machine.refinement).trans
      verified.provider.refinement).trans verified.driver.refinement)

/-- Fundamental behavioral inclusion for every admitted loaded execution. -/
theorem sound (verified : VerifiedProgram spec)
    (execution : (verified.artifact.format.loadedBehavior (emitProgram verified)).system.ExecutionPrefix)
    (terminal : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.Terminal
        execution.state execution.graph)
    (admitted : spec.admits ((verified.artifact.format.loadedBehavior
      (emitProgram verified)).inputOf
        execution.initialState)) :
    spec.accepts
      ((verified.artifact.format.loadedBehavior
        (emitProgram verified)).inputOf
          execution.initialState)
      ((verified.artifact.format.loadedBehavior
        (emitProgram verified)).observe execution) :=
  verified.refinement.preservesAcceptance verified.portable.sound execution terminal admitted

/-- Every admitted input has a coherent loaded execution prefix. -/
theorem execution_nonempty (verified : VerifiedProgram spec)
    (input : spec.Input) (admitted : spec.admits input) :
    Nonempty { execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix //
      (verified.artifact.format.loadedBehavior
        (emitProgram verified)).HasInput
          input execution } :=
  verified.loadedAdequate.execution input admitted

/-- Every reachable finite frontier of the loaded behavior can either reach a
terminal state or continue as an infinite execution. -/
theorem execution_completes (verified : VerifiedProgram spec)
    (execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix) :
    Nonempty ((verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.Completion execution.state execution.graph
        execution.events) := by
  exact verified.loadedAdequate.completion execution

/-- A loaded completion paired with the exact portable completion obtained by
the verified refinement, retaining inspectable transport provenance. -/
structure CompletionRefinement (verified : VerifiedProgram spec)
    (execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix) where
  loaded : (verified.artifact.format.loadedBehavior
    (emitProgram verified)).system.Completion execution.state execution.graph
      execution.events
  portable : verified.portable.behavior.system.Completion
    (verified.refinement.mapPrefix execution).state
    (verified.refinement.mapPrefix execution).graph
    (verified.refinement.mapPrefix execution).events
  exact : portable =
    verified.refinement.mapCompletionAtPrefix execution loaded

/-- Every loaded finite frontier has a completion whose exact image in the
portable behavior is retained by `CompletionRefinement`. -/
theorem completion_refinement_nonempty (verified : VerifiedProgram spec)
    (execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix) :
    Nonempty (CompletionRefinement verified execution) := by
  rcases verified.execution_completes execution with ⟨completion⟩
  exact ⟨{
    loaded := completion
    portable := verified.refinement.mapCompletionAtPrefix execution completion
    exact := rfl
  }⟩

end VerifiedProgram

/-- The canonical parser accepts the exact bytes returned by emission. -/
theorem emitProgram_parses (verified : VerifiedProgram spec) :
    verified.artifact.format.Parses (emitProgram verified)
      verified.artifact.artifact :=
  verified.artifact.format.writeParses verified.artifact.artifact

end Grass
