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

/-- Parsing the emitted bytes selects the exact certified artifact behavior. -/
theorem loadedBehavior_exact (verified : VerifiedProgram spec) :
    verified.artifact.format.loadedBehavior (emitProgram verified) =
      verified.artifact.format.artifactBehavior verified.artifact.artifact :=
  verified.artifact.format.loadExact
    (verified.artifact.format.writeParses verified.artifact.artifact)

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
  verified.loadedBehavior_exact ▸
    verified.artifact.adequate.execution input admitted

/-- Every reachable finite frontier of the loaded behavior can either reach a
terminal state or continue as an infinite execution. -/
theorem execution_completes (verified : VerifiedProgram spec)
    (execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix) :
    Nonempty ((verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.Completion execution.state execution.graph
        execution.events) := by
  exact (ProgramBehavior.Adequate.cast verified.loadedBehavior_exact
    verified.artifact.adequate).completion execution

end VerifiedProgram

/-- The canonical parser accepts the exact bytes returned by emission. -/
theorem emitProgram_parses (verified : VerifiedProgram spec) :
    verified.artifact.format.Parses (emitProgram verified)
      verified.artifact.artifact :=
  verified.artifact.format.writeParses verified.artifact.artifact

end Grass
