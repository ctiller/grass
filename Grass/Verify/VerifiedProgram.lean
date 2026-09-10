import Grass.Refinement.Coverage
import Grass.Spec.Root

/-!
# VerifiedProgramRoot composition

The public gate contains only stratified certificates. Soundness is derived by
composing adjacent relational simulations, and emitted bytes are derived from
the exact certified artifact through its selected canonical writer.

`Grass.VerifiedProgram` below is the resource-indexed name an author writes
(`VerifiedProgram spec` for `spec : SpecProcess resources`); it is reducibly
equal to `VerifiedProgramRoot spec.root`, so every theorem proved above about
`VerifiedProgramRoot` — including `emitProgram` itself — already applies to it
without restatement.
-/

namespace Grass

variable {spec : SpecRoot}

/-- The sole certificate accepted by verified emission. -/
structure VerifiedProgramRoot (spec : SpecRoot) where
  portable : PortableProgramCertificate spec
  driver : ProjectedDriverCertificate portable
  provider : ProviderCertificate driver
  machine : MachineCertificate provider
  artifact : ArtifactCertificate machine

/-- Verified emission invokes the writer selected by the artifact certificate. -/
def emitProgram (verified : VerifiedProgramRoot spec) : ByteArray :=
  verified.artifact.format.write verified.artifact.artifact

namespace VerifiedProgramRoot

/-- Stable identities of every keyed demand declared by the five certificate
tiers from the portable specification through the artifact stage. -/
def requirementKeys (verified : VerifiedProgramRoot spec) : List RequirementKey :=
  verified.artifact.stage.allKeys

/-- `VerifiedProgramRoot.requirementKeys_nodup` proves that no two certificate
tiers discharge the same stable requirement identity. -/
theorem requirementKeys_nodup (verified : VerifiedProgramRoot spec) :
    verified.requirementKeys.Nodup :=
  verified.artifact.allKeys_nodup

/-- Every portable demand identity occurs in the exported requirement keys. -/
theorem portable_identity_mem_requirementKeys (verified : VerifiedProgramRoot spec)
    (key : spec.requirements.Key) :
    spec.requirements.identity key ∈ verified.requirementKeys :=
  verified.artifact.stage.prior_mem_allKeys
    (verified.machine.stage.prior_mem_allKeys
      (verified.provider.stage.prior_mem_allKeys
        (verified.driver.stage.prior_mem_allKeys
          (spec.requirements.identity_mem_identities key))))

/-- Every driver demand identity occurs in the exported requirement keys. -/
theorem driver_identity_mem_requirementKeys (verified : VerifiedProgramRoot spec)
    (key : verified.driver.stage.demands.Key) :
    verified.driver.stage.demands.identity key ∈ verified.requirementKeys :=
  verified.artifact.stage.prior_mem_allKeys
    (verified.machine.stage.prior_mem_allKeys
      (verified.provider.stage.prior_mem_allKeys
        (verified.driver.stage.identity_mem_allKeys key)))

/-- Every provider demand identity occurs in the exported requirement keys. -/
theorem provider_identity_mem_requirementKeys (verified : VerifiedProgramRoot spec)
    (key : verified.provider.stage.demands.Key) :
    verified.provider.stage.demands.identity key ∈ verified.requirementKeys :=
  verified.artifact.stage.prior_mem_allKeys
    (verified.machine.stage.prior_mem_allKeys
      (verified.provider.stage.identity_mem_allKeys key))

/-- Every machine demand identity occurs in the exported requirement keys. -/
theorem machine_identity_mem_requirementKeys (verified : VerifiedProgramRoot spec)
    (key : verified.machine.stage.demands.Key) :
    verified.machine.stage.demands.identity key ∈ verified.requirementKeys :=
  verified.artifact.stage.prior_mem_allKeys
    (verified.machine.stage.identity_mem_allKeys key)

/-- Every artifact demand identity occurs in the exported requirement keys. -/
theorem artifact_identity_mem_requirementKeys (verified : VerifiedProgramRoot spec)
    (key : verified.artifact.stage.demands.Key) :
    verified.artifact.stage.demands.identity key ∈ verified.requirementKeys :=
  verified.artifact.stage.identity_mem_allKeys key

/-- Parsing the emitted bytes selects the exact certified artifact behavior. -/
theorem loadedBehavior_exact (verified : VerifiedProgramRoot spec) :
    verified.artifact.format.loadedBehavior (emitProgram verified) =
      verified.artifact.format.artifactBehavior verified.artifact.artifact :=
  verified.artifact.format.loadExact
    (verified.artifact.format.writeParses verified.artifact.artifact)

/-- The exact behavior loaded from emitted bytes inherits the artifact
certificate's paired execution and completion adequacy guarantee. -/
theorem loadedAdequate (verified : VerifiedProgramRoot spec) :
    (verified.artifact.format.loadedBehavior (emitProgram verified)).Adequate :=
  ProgramBehavior.Adequate.cast verified.loadedBehavior_exact
    verified.artifact.adequate

/-- Loaded artifact behavior refines the portable process behavior. -/
def refinement (verified : VerifiedProgramRoot spec) :
    BehaviorRefinement
      (verified.artifact.format.loadedBehavior (emitProgram verified))
      verified.portable.behavior :=
  BehaviorRefinement.castConcrete verified.loadedBehavior_exact
    (((verified.artifact.refinement.trans verified.machine.refinement).trans
      verified.provider.refinement).trans verified.driver.refinement)

/-- Loaded behavior and the certificate-selected portable behavior cover the
same currently represented finite and divergent histories. This does not make
`ProgramBehavior` an authoritative relational semantics of `SpecRoot`;
author liveness and fairness remain separate demands. -/
theorem coverage (verified : VerifiedProgramRoot spec) :
    BehaviorRefinement.Coverage verified.refinement :=
  BehaviorRefinement.Coverage.castConcrete verified.loadedBehavior_exact
    (((verified.artifact.coverage.trans verified.machine.coverage).trans
      verified.provider.coverage).trans verified.driver.coverage)

/-- Every represented history of the selected portable behavior has an exact
loaded preimage. -/
theorem histories_surjective (verified : VerifiedProgramRoot spec) :
    Function.Surjective verified.refinement.mapHistory :=
  verified.coverage.histories

/-- Fundamental behavioral inclusion for every admitted loaded execution. -/
theorem sound (verified : VerifiedProgramRoot spec)
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
theorem execution_nonempty (verified : VerifiedProgramRoot spec)
    (input : spec.Input) (admitted : spec.admits input) :
    Nonempty { execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix //
      (verified.artifact.format.loadedBehavior
        (emitProgram verified)).HasInput
          input execution } :=
  verified.loadedAdequate.execution input admitted

/-- Every reachable finite frontier of the loaded behavior can either reach a
terminal state or continue as an infinite execution. -/
theorem execution_completes (verified : VerifiedProgramRoot spec)
    (execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix) :
    Nonempty ((verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.Completion execution.state execution.graph
        execution.events) := by
  exact verified.loadedAdequate.completion execution

/-- A loaded completion paired with the exact portable completion obtained by
the verified refinement, retaining inspectable transport provenance. -/
structure CompletionRefinement (verified : VerifiedProgramRoot spec)
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
theorem completion_refinement_nonempty (verified : VerifiedProgramRoot spec)
    (execution : (verified.artifact.format.loadedBehavior
      (emitProgram verified)).system.ExecutionPrefix) :
    Nonempty (CompletionRefinement verified execution) := by
  rcases verified.execution_completes execution with ⟨completion⟩
  exact ⟨{
    loaded := completion
    portable := verified.refinement.mapCompletionAtPrefix execution completion
    exact := rfl
  }⟩

end VerifiedProgramRoot

/-- The canonical parser accepts the exact bytes returned by emission. -/
theorem emitProgram_parses (verified : VerifiedProgramRoot spec) :
    verified.artifact.format.Parses (emitProgram verified)
      verified.artifact.artifact :=
  verified.artifact.format.writeParses verified.artifact.artifact

/-- The resource-indexed certificate a spike's `Spec.lean` states its gate
against. `spec.root` recomputes the unindexed `SpecRoot` every certificate
tier above actually consumes, so this is definitionally
`VerifiedProgramRoot spec.root` and not a second, independent gate. -/
abbrev VerifiedProgram {R : Type} [Resource.ResourceModel R] {resources : R}
    (spec : SpecProcess resources) := VerifiedProgramRoot spec.root

end Grass
