import Grass.Trust.Audit

namespace Grass.Tests.Foundation

inductive NoDemand

def noDemands : DemandFamily where
  Key := NoDemand
  keys := []
  complete := fun key => nomatch key
  unique := by simp
  identity := fun key => nomatch key
  identityInjective := fun left => nomatch left
  kind := fun key => nomatch key
  statement := fun key => nomatch key

theorem noDemandCertificates : DemandCertificateFamily noDemands where
  discharge := fun key => nomatch key

namespace DemandIdentityFixture

def prior : RequirementKey := ⟨⟨"foundation-fixture", "prior"⟩⟩

def identity : Bool → RequirementKey
  | false => ⟨⟨"foundation-fixture", "false"⟩⟩
  | true => ⟨⟨"foundation-fixture", "true"⟩⟩

def demands : DemandFamily where
  Key := Bool
  keys := [false, true]
  complete := by intro key; cases key <;> simp
  unique := by simp
  identity := identity
  identityInjective := by
    intro left right equal
    cases left <;> cases right <;> simp_all [identity]
  kind := fun _ => .functional
  statement := fun _ => True

def stage : DerivedDemandFamily [prior] where
  demands := demands
  origin := fun _ => .external ⟨"foundation-fixture", "authority"⟩
  fresh := by intro key; cases key <;> simp [demands, identity, prior]

example (key : demands.Key) : demands.identity key ∈ demands.identities := by simp

example : demands.identities.Nodup := demands.identities_nodup

example : prior ∈ stage.allKeys := stage.prior_mem_allKeys (by simp)

example (key : stage.demands.Key) :
    stage.demands.identity key ∈ stage.allKeys := by simp

example : stage.allKeys.Nodup := stage.allKeys_nodup (by simp)

inductive FinalDemand
  | only

def finalIdentity : FinalDemand → RequirementKey
  | .only => ⟨⟨"foundation-fixture", "final"⟩⟩

def finalDemands : DemandFamily where
  Key := FinalDemand
  keys := [.only]
  complete := by intro key; cases key; simp
  unique := by simp
  identity := finalIdentity
  identityInjective := by intro left right _; cases left; cases right; rfl
  kind := fun _ => .artifact
  statement := fun _ => True

def finalStage : DerivedDemandFamily stage.allKeys where
  demands := finalDemands
  origin := fun _ => .external ⟨"foundation-fixture", "final-authority"⟩
  fresh := by
    intro key
    cases key
    simp [stage, demands, identity, prior, finalDemands, finalIdentity,
      DerivedDemandFamily.allKeys, DemandFamily.identities]

example : finalStage.allKeys.Nodup :=
  finalStage.allKeys_nodup (stage.allKeys_nodup (by simp))

end DemandIdentityFixture

def noDerivedDemands : DerivedDemandFamily noDemands.identities where
  demands := noDemands
  origin := fun key => nomatch key
  fresh := fun derived => nomatch derived

abbrev spec : SpecProcess where
  Input := Bool
  AuditEvent := Bool
  Observation := Bool
  admits := fun _ => True
  observationProjection := .identity Bool
  accepts := fun _ _ => True
  requirements := noDemands
  evidenceRelevant := fun _ _ => false

namespace ObservationProjectionFixture

def boolToNat : ObservationProjection Bool Nat where
  project := List.map Bool.toNat

def natToString : ObservationProjection Nat String where
  project := List.map toString

def stringLengths : ObservationProjection String Nat where
  project := List.map String.length

example : (ObservationProjection.identity Nat).comp boolToNat = boolToNat := by
  simp

example : boolToNat.comp (ObservationProjection.identity Bool) = boolToNat := by
  simp

example : (stringLengths.comp natToString).comp boolToNat =
    stringLengths.comp (natToString.comp boolToNat) := by
  simp

end ObservationProjectionFixture

def system : RelationalSystem spec.AuditEvent where
  State := Bool
  Choice := Unit
  Graph := Nat
  Initial := fun _ graph => graph = 0
  Step := fun _ _ _ _ _ _ => False
  Terminal := fun _ _ => True
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := Nat.le
  extendsRefl := Nat.le_refl
  extendsTrans := Nat.le_trans
  stepExtends := fun transition => False.elim transition

def behavior : ProgramBehavior spec where
  system := system
  inputOf := id

def initialExecution (input : Bool) : system.ExecutionPrefix :=
  @RelationalSystem.ExecutionPrefix.initial spec.AuditEvent system input (0 : Nat)
    rfl

example {initialState state : system.State} {initialGraph graph : system.Graph}
    {events : List spec.AuditEvent}
    (execution : system.Runs initialState initialGraph state graph events) : True := by
  induction execution with
  | initial _ => trivial
  | step _ _ _ => trivial

theorem behaviorAdequate : behavior.Adequate where
  execution input _ := ⟨initialExecution input, rfl⟩
  completion _ := ⟨.finite .refl trivial⟩

def behaviorRefinesItself : BehaviorRefinement behavior behavior :=
  .refl behavior

def finiteCompletion (input : Bool) : system.Completion
    (initialExecution input).state (initialExecution input).graph
    (initialExecution input).events :=
  .finite .refl trivial

example (refinement : BehaviorRefinement behavior behavior) (state : system.State) :
    ((BehaviorRefinement.refl behavior).trans refinement).mapState state =
      refinement.mapState state := rfl

example (refinement : BehaviorRefinement behavior behavior) (graph : system.Graph) :
    (refinement.trans (BehaviorRefinement.refl behavior)).mapGraph graph =
      refinement.mapGraph graph := rfl

example (first second third : BehaviorRefinement behavior behavior)
    (state : system.State) :
    ((first.trans second).trans third).mapState state =
      (first.trans (second.trans third)).mapState state := rfl

example : (BehaviorRefinement.refl behavior).mapCompletion
    (finiteCompletion true) = finiteCompletion true :=
  BehaviorRefinement.mapCompletion_refl behavior (finiteCompletion true)

example : (behaviorRefinesItself.trans behaviorRefinesItself).mapCompletion
    (finiteCompletion true) =
      behaviorRefinesItself.mapCompletion
        (behaviorRefinesItself.mapCompletion (finiteCompletion true)) :=
  BehaviorRefinement.mapCompletion_trans behaviorRefinesItself
    behaviorRefinesItself (finiteCompletion true)

def portable : PortableProgramCertificate spec where
  behavior := behavior
  requirements := noDemandCertificates
  adequate := behaviorAdequate
  sound := fun _ _ _ => trivial

def driver : ProjectedDriverCertificate portable where
  behavior := behavior
  refinement := behaviorRefinesItself
  adequate := behaviorAdequate
  stage := noDerivedDemands
  requirements := noDemandCertificates

def provider : ProviderCertificate driver where
  behavior := behavior
  refinement := behaviorRefinesItself
  adequate := behaviorAdequate
  stage := noDerivedDemands
  requirements := noDemandCertificates

def machine : MachineCertificate provider where
  behavior := behavior
  refinement := behaviorRefinesItself
  adequate := behaviorAdequate
  stage := noDerivedDemands
  requirements := noDemandCertificates

def artifactFormat : ArtifactFormat spec where
  Artifact := Unit
  write := fun _ => ByteArray.empty
  Parses := fun bytes _ => bytes = ByteArray.empty
  writeParses := fun _ => rfl
  parseExact := fun parsed => parsed
  artifactBehavior := fun _ => behavior
  loadedBehavior := fun _ => behavior
  loadExact := fun _ => rfl

def artifact : ArtifactCertificate machine where
  format := artifactFormat
  artifact := ()
  refinement := behaviorRefinesItself
  adequate := behaviorAdequate
  stage := noDerivedDemands
  requirements := noDemandCertificates

def verified : VerifiedProgram spec where
  portable := portable
  driver := driver
  provider := provider
  machine := machine
  artifact := artifact

abbrev Certified := VerifiedProgram spec

def aliasedVerified : Certified := verified

def inferredVerified := verified

example : spec.accepts true
    ((artifactFormat.loadedBehavior ByteArray.empty).observe (initialExecution true)) :=
  verified.sound (initialExecution true) trivial trivial

example : (artifactFormat.loadedBehavior (emitProgram verified)).Adequate :=
  verified.loadedAdequate

example : Nonempty { execution :
    (artifactFormat.loadedBehavior ByteArray.empty).system.ExecutionPrefix //
    (artifactFormat.loadedBehavior ByteArray.empty).HasInput true execution } :=
  verified.execution_nonempty true trivial

example : Nonempty ((artifactFormat.loadedBehavior ByteArray.empty).system.Completion
    (initialExecution true).state (initialExecution true).graph
      (initialExecution true).events) :=
  verified.execution_completes (initialExecution true)

example : Nonempty (VerifiedProgram.CompletionRefinement verified
    (initialExecution true)) :=
  verified.completion_refinement_nonempty (initialExecution true)

example (completion : VerifiedProgram.CompletionRefinement verified
    (initialExecution true)) :
    completion.portable = verified.refinement.mapCompletionAtPrefix
      (initialExecution true) completion.loaded :=
  completion.exact

example : verified.requirementKeys.Nodup := verified.requirementKeys_nodup

namespace VerifiedRequirementFixture

/-- One nonempty keyed demand, parameterized by its certificate tier. -/
def keyed (tier : String) : DemandFamily where
  Key := Unit
  keys := [()]
  complete := by intro key; cases key; simp
  unique := by simp
  identity := fun _ => ⟨⟨"verified-ledger", tier⟩⟩
  identityInjective := by intro left right _; cases left; cases right; rfl
  kind := fun _ => .functional
  statement := fun _ => True

theorem certificates (tier : String) : DemandCertificateFamily (keyed tier) where
  discharge := fun _ => trivial

def stage (prior : List RequirementKey) (tier : String)
    (fresh : ⟨⟨"verified-ledger", tier⟩⟩ ∉ prior) :
    DerivedDemandFamily prior where
  demands := keyed tier
  origin := fun _ => .external ⟨"verified-ledger", tier ++ "-authority"⟩
  fresh := by intro key; cases key; exact fresh

def spec : SpecProcess where
  Input := Bool
  AuditEvent := Bool
  Observation := Bool
  admits := fun _ => True
  observationProjection := .identity Bool
  accepts := fun _ _ => True
  requirements := keyed "portable"

def system : RelationalSystem spec.AuditEvent where
  State := Bool
  Choice := Unit
  Graph := Nat
  Initial := fun _ graph => graph = 0
  Step := fun _ _ _ _ _ _ => False
  Terminal := fun _ _ => True
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := Nat.le
  extendsRefl := Nat.le_refl
  extendsTrans := Nat.le_trans
  stepExtends := fun transition => False.elim transition

def behavior : ProgramBehavior spec where
  system := system
  inputOf := id

def initialExecution (input : Bool) : system.ExecutionPrefix :=
  @RelationalSystem.ExecutionPrefix.initial spec.AuditEvent system input (0 : Nat)
    rfl

theorem adequate : behavior.Adequate where
  execution input _ := ⟨initialExecution input, rfl⟩
  completion _ := ⟨.finite .refl trivial⟩

def portable : PortableProgramCertificate spec where
  behavior := behavior
  requirements := certificates "portable"
  adequate := adequate
  sound := fun _ _ _ => trivial

def driverStage : DerivedDemandFamily spec.requirements.identities :=
  stage spec.requirements.identities "driver" (by
    simp [spec, keyed, DemandFamily.identities])

def driver : ProjectedDriverCertificate portable where
  behavior := behavior
  refinement := .refl behavior
  adequate := adequate
  stage := driverStage
  requirements := certificates "driver"

def providerStage : DerivedDemandFamily driver.stage.allKeys :=
  stage driver.stage.allKeys "provider" (by
    simp [driver, driverStage, stage, spec, keyed,
      DemandFamily.identities, DerivedDemandFamily.allKeys])

def provider : ProviderCertificate driver where
  behavior := behavior
  refinement := .refl behavior
  adequate := adequate
  stage := providerStage
  requirements := certificates "provider"

def machineStage : DerivedDemandFamily provider.stage.allKeys :=
  stage provider.stage.allKeys "machine" (by
    simp [provider, providerStage, driver, driverStage, stage, spec, keyed,
      DemandFamily.identities, DerivedDemandFamily.allKeys])

def machine : MachineCertificate provider where
  behavior := behavior
  refinement := .refl behavior
  adequate := adequate
  stage := machineStage
  requirements := certificates "machine"

def artifactFormat : ArtifactFormat spec where
  Artifact := Unit
  write := fun _ => ByteArray.empty
  Parses := fun bytes _ => bytes = ByteArray.empty
  writeParses := fun _ => rfl
  parseExact := fun parsed => parsed
  artifactBehavior := fun _ => behavior
  loadedBehavior := fun _ => behavior
  loadExact := fun _ => rfl

def artifactStage : DerivedDemandFamily machine.stage.allKeys :=
  stage machine.stage.allKeys "artifact" (by
    simp [machine, machineStage, provider, providerStage, driver, driverStage,
      stage, spec, keyed, DemandFamily.identities,
      DerivedDemandFamily.allKeys])

def artifact : ArtifactCertificate machine where
  format := artifactFormat
  artifact := ()
  refinement := .refl behavior
  adequate := adequate
  stage := artifactStage
  requirements := certificates "artifact"

def verified : VerifiedProgram spec where
  portable := portable
  driver := driver
  provider := provider
  machine := machine
  artifact := artifact

example : verified.requirementKeys = [
    ⟨⟨"verified-ledger", "portable"⟩⟩,
    ⟨⟨"verified-ledger", "driver"⟩⟩,
    ⟨⟨"verified-ledger", "provider"⟩⟩,
    ⟨⟨"verified-ledger", "machine"⟩⟩,
    ⟨⟨"verified-ledger", "artifact"⟩⟩] := rfl

example : spec.requirements.identity () ∈ verified.requirementKeys :=
  verified.portable_identity_mem_requirementKeys ()

example : driver.stage.demands.identity () ∈ verified.requirementKeys :=
  verified.driver_identity_mem_requirementKeys ()

example : provider.stage.demands.identity () ∈ verified.requirementKeys :=
  verified.provider_identity_mem_requirementKeys ()

example : machine.stage.demands.identity () ∈ verified.requirementKeys :=
  verified.machine_identity_mem_requirementKeys ()

example : artifact.stage.demands.identity () ∈ verified.requirementKeys :=
  verified.artifact_identity_mem_requirementKeys ()

example : verified.requirementKeys.Nodup := verified.requirementKeys_nodup

end VerifiedRequirementFixture

namespace InfinitePrefixFixture

/-- A nontrivial fixture whose infinite limit condition inspects both the event
already taken and the first event of its suffix. -/
def system : RelationalSystem Bool where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun priorEvents _ _ _ eventAt =>
    priorEvents = [true] ∧ eventAt 0 = false
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

def emptyPrefix : system.ExecutionPrefix :=
  RelationalSystem.ExecutionPrefix.initial (system := system)
    (state := ()) (graph := ()) trivial

theorem firstStep : system.Step emptyPrefix.graph emptyPrefix.state () true () () :=
  trivial

def samplePrefix : system.ExecutionPrefix :=
  emptyPrefix.step firstStep

theorem falseSuffix : system.Steps samplePrefix.state samplePrefix.graph [false] () () :=
  .step (choice := ()) .refl trivial

theorem trueSuffix : system.Steps () () [true] () () :=
  .step (choice := ()) .refl trivial

abbrev behavior : ProgramBehavior spec where
  system := system
  inputOf := fun _ => false

def refinement : BehaviorRefinement behavior behavior :=
  .refl behavior

abbrev abstractSystem : RelationalSystem Bool where
  State := Bool
  Choice := Nat
  Graph := Nat
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

abbrev abstractBehavior : ProgramBehavior spec where
  system := abstractSystem
  inputOf := fun _ => false

def toAbstract : BehaviorRefinement behavior abstractBehavior :=
  BehaviorRefinement.lockstep (fun _ => false) (fun _ => 0) (fun _ => 0)
    (fun _ => rfl) (fun _ => trivial) (fun _ => trivial)
    (fun terminal => False.elim terminal) (fun _ => trivial)

abbrev highestSystem : RelationalSystem Bool where
  State := Nat
  Choice := Bool
  Graph := Bool
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

abbrev highestBehavior : ProgramBehavior spec where
  system := highestSystem
  inputOf := fun _ => false

def toHighest : BehaviorRefinement abstractBehavior highestBehavior :=
  BehaviorRefinement.lockstep Bool.toNat (fun _ => true) (fun _ => false)
    (fun _ => rfl) (fun _ => trivial) (fun _ => trivial)
    (fun terminal => False.elim terminal) (fun _ => trivial)

example : (samplePrefix.append falseSuffix).events = [true, false] := rfl

example : (samplePrefix.append falseSuffix).append trueSuffix =
    samplePrefix.append (falseSuffix.trans trueSuffix) :=
  RelationalSystem.ExecutionPrefix.append_assoc samplePrefix falseSuffix trueSuffix

example : samplePrefix.append (.refl) = samplePrefix := by simp

example : refinement.mapPrefix samplePrefix = samplePrefix := by
  change (BehaviorRefinement.refl behavior).mapPrefix samplePrefix = samplePrefix
  exact BehaviorRefinement.mapPrefix_refl behavior samplePrefix

example : toAbstract.mapPrefix emptyPrefix =
    RelationalSystem.ExecutionPrefix.initial (system := abstractSystem)
      (state := false) (graph := 0)
      (toAbstract.initial (state := ()) (graph := ()) trivial) :=
  BehaviorRefinement.mapPrefix_initial toAbstract trivial

example : toAbstract.mapPrefix samplePrefix =
    (toAbstract.mapPrefix emptyPrefix).append
      (toAbstract.mapSteps (.step .refl firstStep)) := by
  change toAbstract.mapPrefix (emptyPrefix.step firstStep) = _
  exact BehaviorRefinement.mapPrefix_step toAbstract emptyPrefix firstStep

example : (toAbstract.trans toHighest).mapPrefix samplePrefix =
    toHighest.mapPrefix (toAbstract.mapPrefix samplePrefix) :=
  BehaviorRefinement.mapPrefix_trans toAbstract toHighest samplePrefix

example : toAbstract.mapPrefix (samplePrefix.append falseSuffix) =
    (toAbstract.mapPrefix samplePrefix).append
      (toAbstract.mapSteps falseSuffix) := by
  exact BehaviorRefinement.mapPrefix_append
    toAbstract samplePrefix falseSuffix

example : (toAbstract.mapPrefix samplePrefix).events =
    toAbstract.lens.project samplePrefix.events :=
  BehaviorRefinement.mapPrefix_events toAbstract samplePrefix

example : abstractBehavior.observe (toAbstract.mapPrefix samplePrefix) =
    behavior.observe samplePrefix :=
  BehaviorRefinement.observe_mapPrefix toAbstract samplePrefix

example : abstractBehavior.inputOf (toAbstract.mapPrefix samplePrefix).initialState =
    behavior.inputOf samplePrefix.initialState :=
  BehaviorRefinement.inputOf_mapPrefix toAbstract samplePrefix

example : abstractBehavior.HasInput false (toAbstract.mapPrefix samplePrefix) ↔
    behavior.HasInput false samplePrefix :=
  BehaviorRefinement.hasInput_mapPrefix toAbstract false samplePrefix

example (terminal : system.Terminal samplePrefix.state samplePrefix.graph) :
    abstractBehavior.system.Terminal (toAbstract.mapPrefix samplePrefix).state
      (toAbstract.mapPrefix samplePrefix).graph :=
  BehaviorRefinement.terminal_mapPrefix toAbstract samplePrefix terminal

def continuation : system.InfiniteContinuation samplePrefix.state samplePrefix.graph
    samplePrefix.events where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => false
  stateZero := rfl
  graphZero := rfl
  step := fun _ => trivial
  consistent := ⟨rfl, rfl⟩

example : (toAbstract.mapInfinite continuation).prefixEvents 2 =
    continuation.prefixEvents 2 :=
  toAbstract.mapInfinite_prefixEvents continuation 2

example : abstractSystem.Steps
    (toAbstract.mapState samplePrefix.state)
    (toAbstract.mapGraph samplePrefix.graph)
    (continuation.prefixEvents 2)
    (toAbstract.mapState (continuation.stateAt 2))
    (toAbstract.mapGraph (continuation.graphAt 2)) :=
  toAbstract.mapInfinite_prefixSteps continuation 2

/-- A non-vacuous indexed continuation: state and graph both advance at every
step, while its observable events alternate. -/
abbrev indexedSystem : RelationalSystem Bool where
  State := Nat
  Choice := Unit
  Graph := Nat
  Initial := fun state graph => state = 0 ∧ graph = 0
  Step := fun before state _ event next after =>
    next = state + 1 ∧ after = before + 1 ∧ event = (state % 2 == 1)
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun before after => before ≤ after
  extendsRefl := Nat.le_refl
  extendsTrans := Nat.le_trans
  stepExtends := fun transition => transition.2.1 ▸ Nat.le_succ _

abbrev indexedContinuation : indexedSystem.InfiniteContinuation 0 0 [] where
  stateAt := fun index => index
  graphAt := fun index => index
  choiceAt := fun _ => ()
  eventAt := fun index => index % 2 == 1
  stateZero := rfl
  graphZero := rfl
  step := fun _ => ⟨rfl, rfl, rfl⟩
  consistent := trivial

theorem indexedPrefixEvents :
    indexedContinuation.prefixEvents 3 = [false, true, false] := rfl

example : indexedSystem.Steps 0 0 [false, true, false] 3 3 := by
  rw [← indexedPrefixEvents]
  exact indexedContinuation.prefixSteps 3

example : indexedSystem.Extends 0 (indexedContinuation.graphAt 3) :=
  indexedContinuation.graphExtendsAt 3

def completion : system.Completion samplePrefix.state samplePrefix.graph samplePrefix.events :=
  .infinite continuation

example : ((BehaviorRefinement.refl behavior).mapInfinite continuation).prefixEvents 3 =
    continuation.prefixEvents 3 := rfl

example : (BehaviorRefinement.refl behavior).mapInfinite continuation = continuation :=
  BehaviorRefinement.mapInfinite_refl behavior continuation

example : ((toAbstract.trans toHighest).mapInfinite continuation).prefixEvents 3 =
    (toHighest.mapInfinite (toAbstract.mapInfinite continuation)).prefixEvents 3 := rfl

example : (toAbstract.trans toHighest).mapInfinite continuation =
    toHighest.mapInfinite (toAbstract.mapInfinite continuation) :=
  BehaviorRefinement.mapInfinite_trans toAbstract toHighest continuation

example : (toAbstract.trans toHighest).mapCompletion completion =
    toHighest.mapCompletion (toAbstract.mapCompletion completion) :=
  BehaviorRefinement.mapCompletion_trans toAbstract toHighest completion

example : InfiniteRefinement toAbstract.lens toAbstract.mapState toAbstract.mapGraph
    continuation :=
  toAbstract.mapInfinite_prefixes continuation

def mappedCompletion : abstractBehavior.system.Completion
    (toAbstract.mapPrefix samplePrefix).state
    (toAbstract.mapPrefix samplePrefix).graph
    (toAbstract.mapPrefix samplePrefix).events :=
  toAbstract.mapCompletionAtPrefix samplePrefix completion

example : samplePrefix.events = [true] := rfl

end InfinitePrefixFixture

namespace WeakSegmentRefinementFixture

inductive Event where
  | internal
  | visible (value : Nat)
  | safety
deriving DecidableEq

inductive SafetyKey where
  | audit

def safetyDemands : DemandFamily where
  Key := SafetyKey
  keys := [.audit]
  complete := fun key => by cases key; simp
  unique := by simp
  identity := fun _ => ⟨⟨"foundation-test", "safety-audit"⟩⟩
  identityInjective := fun left right _ => by cases left; cases right; rfl
  kind := fun _ => .safety
  statement := fun _ => True

/-- The functional view hides both implementation work and the independent
safety marker. -/
def observations : ObservationProjection Event Nat where
  project events := events.filterMap fun
    | .visible value => some value
    | _ => none

abbrev spec : SpecProcess where
  Input := Unit
  AuditEvent := Event
  Observation := Nat
  admits := fun _ => True
  observationProjection := observations
  accepts := fun _ _ => True
  requirements := safetyDemands
  evidenceRelevant := fun key event =>
    decide (key = safetyDemands.identity .audit ∧ event = .safety)

/-- Internal implementation events have zero denotation; visible and safety
events remain in the abstract audit trace. -/
def hideInternal : RefinementLens spec where
  project events := events.filter fun event => decide (event ≠ .internal)
  project_nil := rfl
  project_append := List.filter_append
  observationExact events := by
    induction events with
    | nil => rfl
    | cons event events inductionHypothesis =>
        change observations.project
          (List.filter (fun event => decide (event ≠ .internal)) events) =
          observations.project events at inductionHypothesis
        cases event <;> simpa [observations] using inductionHypothesis
  evidenceNonErasing key events := by
    by_cases selected : key = safetyDemands.identity .audit
    · subst key
      induction events with
      | nil => simp
      | cons event events inductionHypothesis =>
          cases event <;> simp_all
    · induction events with
      | nil => simp
      | cons event events inductionHypothesis =>
          cases event <;> simp_all

abbrev ConcreteState := Nat × Nat

/-- A finite machine region: internal instructions retain the logical state;
all other instructions may cross an abstract boundary. -/
abbrev concreteSystem : RelationalSystem Event where
  State := ConcreteState
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ before _ event after _ =>
    event = .internal -> after.1 = before.1
  Terminal := fun _ _ => True
  InfiniteConsistent := fun _ _ _ _ _ => False
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

abbrev abstractSystem : RelationalSystem Event where
  State := Nat
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => True
  Terminal := fun _ _ => True
  InfiniteConsistent := fun _ _ _ _ _ => False
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

def concrete : ProgramBehavior spec where
  system := concreteSystem
  inputOf := fun _ => ()

def abstract : ProgramBehavior spec where
  system := abstractSystem
  inputOf := fun _ => ()

theorem segment {state finalState : concreteSystem.State}
    {graph finalGraph : concreteSystem.Graph} {events : List Event}
    (steps : concreteSystem.Steps state graph events finalState finalGraph) :
    abstractSystem.Steps state.1 graph (hideInternal.project events)
      finalState.1 finalGraph := by
  induction steps with
  | refl => exact .refl
  | step prior transition inductionHypothesis =>
      rename_i prefixEvents current currentGraph choice event next nextGraph
      by_cases internal : event = .internal
      · have same : next.1 = current.1 := transition internal
        subst event
        simpa [hideInternal, same] using inductionHypothesis
      · rw [hideInternal.project_append]
        have selected : hideInternal.project [event] = [event] := by
          simp [hideInternal, internal]
        rw [selected]
        exact RelationalSystem.Steps.step inductionHypothesis (choice := ()) trivial

def refinement : BehaviorRefinement concrete abstract where
  lens := hideInternal
  mapState := Prod.fst
  mapGraph := id
  input := fun _ => rfl
  initial := fun _ => trivial
  segment := segment
  terminal := fun _ => trivial
  infinite execution := False.elim execution.consistent

theorem insertedInstruction : concreteSystem.Steps (0, 0) () [.internal]
    (0, 1) () :=
  .step (choice := ()) .refl (fun _ => rfl)

example : abstractSystem.Steps 0 () [] 0 () := by
  simpa [refinement, concrete, abstract, hideInternal] using
    refinement.mapSteps insertedInstruction

theorem loweredInstruction : concreteSystem.Step () (0, 1) () (.visible 7)
    (1, 2) () := by
  intro impossible
  cases impossible

theorem loweredRegion : concreteSystem.Steps (0, 0) ()
    [.internal, .visible 7] (1, 2) () :=
  .step insertedInstruction loweredInstruction

example : abstractSystem.Steps 0 () [.visible 7] 1 () := by
  simpa [refinement, concrete, abstract, hideInternal] using
    refinement.mapSteps loweredRegion

/-- Two concrete branch summaries select their respective exact abstract
segments through the same refinement. -/
theorem branchOne : concreteSystem.Steps (0, 0) () [.visible 1] (1, 1) () :=
  .step (choice := ()) .refl (fun impossible => nomatch impossible)

theorem branchTwo : concreteSystem.Steps (0, 0) () [.visible 2] (1, 1) () :=
  .step (choice := ()) .refl (fun impossible => nomatch impossible)

example :
    abstractSystem.Steps 0 () [.visible 1] 1 () ∧
      abstractSystem.Steps 0 () [.visible 2] 1 () := by
  constructor
  · simpa [refinement, concrete, abstract, hideInternal] using
      refinement.mapSteps branchOne
  · simpa [refinement, concrete, abstract, hideInternal] using
      refinement.mapSteps branchTwo

theorem safetyRetained :
    ([.safety].filter
      (spec.evidenceRelevant (safetyDemands.identity .audit))).Sublist
      ((hideInternal.project [.safety]).filter
        (spec.evidenceRelevant (safetyDemands.identity .audit))) :=
  hideInternal.evidenceNonErasing (safetyDemands.identity .audit) [.safety]

example : observations.project [.safety] = [] := rfl

example : abstract.observe (refinement.mapPrefix {
    initialState := (0, 0)
    initialGraph := ()
    state := (1, 2)
    graph := ()
    events := [.internal, .visible 7]
    runs := RelationalSystem.Runs.ofInitialSteps trivial loweredRegion }) =
    [7] := rfl

/-- A concrete infinite internal loop cannot refine a behavior with no step at
all: finite zero-denotation alone does not hide divergence. -/
abbrev loopSystem : RelationalSystem Event where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ event _ _ => event = .internal
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

abbrev stoppedSystem : RelationalSystem Event where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ _ _ _ => False
  Terminal := fun _ _ => True
  InfiniteConsistent := fun _ _ _ _ _ => False
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun impossible => False.elim impossible

def loopBehavior : ProgramBehavior spec where
  system := loopSystem
  inputOf := fun _ => ()

def stoppedBehavior : ProgramBehavior spec where
  system := stoppedSystem
  inputOf := fun _ => ()

def internalLoop : loopSystem.InfiniteContinuation () () [] where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => .internal
  stateZero := rfl
  graphZero := rfl
  step := fun _ => rfl
  consistent := trivial

theorem internalLoop_erased (length : Nat) :
    hideInternal.project (internalLoop.prefixEvents length) = [] := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      rw [RelationalSystem.InfiniteContinuation.prefixEvents,
        hideInternal.project_append, inductionHypothesis]
      rfl

theorem internalLoop_prefixEvents (length : Nat) :
    internalLoop.prefixEvents length = List.replicate length Event.internal := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      rw [RelationalSystem.InfiniteContinuation.prefixEvents, inductionHypothesis]
      change List.replicate length Event.internal ++ [Event.internal] =
        List.replicate (length + 1) Event.internal
      exact List.replicate_succ'.symm

theorem hiddenLoopRejected
    (claimed : BehaviorRefinement loopBehavior stoppedBehavior) : False :=
  (claimed.mapInfinite internalLoop).step 0

/-- Interactive divergence is accepted when the abstraction supplies the same
infinite visible progress. -/
abbrev interactiveSystem : RelationalSystem Event where
  State := Unit
  Choice := Unit
  Graph := Unit
  Initial := fun _ _ => True
  Step := fun _ _ _ event _ _ => event = .visible 0
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

def interactiveBehavior : ProgramBehavior spec where
  system := interactiveSystem
  inputOf := fun _ => ()

def interactiveExecution : interactiveSystem.InfiniteContinuation () () [] where
  stateAt := fun _ => ()
  graphAt := fun _ => ()
  choiceAt := fun _ => ()
  eventAt := fun _ => .visible 0
  stateZero := rfl
  graphZero := rfl
  step := fun _ => rfl
  consistent := trivial

/-- Cofinality, not mere target inhabitation, rejects erasing the internal loop
into an abstraction whose only divergence emits visible progress. -/
theorem hiddenLoopCofinalityRejected
    (claimed : InfiniteRefinement (concrete := loopBehavior)
      (abstract := interactiveBehavior) hideInternal (fun _ => ()) (fun _ => ())
      internalLoop) : False := by
  obtain ⟨concreteLength, coverage⟩ := claimed.abstractPrefix 1
  have visible := claimed.abstractExecution.step 0
  have erased := internalLoop_erased concreteLength
  have projectedEmpty :
      (hideInternal.project (internalLoop.prefixEvents concreteLength)).IsPrefix [] := by
    rw [erased]
    exact ⟨[], rfl⟩
  have coverageNil := List.IsPrefix.trans coverage projectedEmpty
  change claimed.abstractExecution.eventAt 0 = .visible 0 at visible
  simp [RelationalSystem.InfiniteContinuation.prefixEvents, visible] at coverageNil

abbrev interactiveAbstractSystem : RelationalSystem Event where
  State := Bool
  Choice := Nat
  Graph := Bool
  Initial := fun _ _ => True
  Step := fun _ _ _ event _ _ => event = .visible 0
  Terminal := fun _ _ => False
  InfiniteConsistent := fun _ _ _ _ _ => True
  Extends := fun _ _ => True
  extendsRefl := fun _ => trivial
  extendsTrans := fun _ _ => trivial
  stepExtends := fun _ => trivial

def interactiveAbstractBehavior : ProgramBehavior spec where
  system := interactiveAbstractSystem
  inputOf := fun _ => ()

def matchedInteractive : BehaviorRefinement interactiveBehavior
    interactiveAbstractBehavior :=
  BehaviorRefinement.lockstep (concrete := interactiveBehavior)
    (abstract := interactiveAbstractBehavior)
    (fun _ : Unit => false) (fun _ : Unit => false) (fun _ : Unit => (0 : Nat))
    (fun _ => rfl) (fun _ => trivial) (fun step => step)
    (fun terminal => False.elim terminal) (fun _ => trivial)

example : InfiniteRefinement matchedInteractive.lens matchedInteractive.mapState
    matchedInteractive.mapGraph interactiveExecution :=
  matchedInteractive.mapInfinite_prefixes interactiveExecution

/-- Expand one event into its selected abstract audit segment. -/
def expandEvent : Event -> List Event
  | .internal => [.internal, .internal]
  | event => [event]

theorem expandEvent_preservesEvidence (key : RequirementKey) (events : List Event) :
    (events.flatMap expandEvent).filter (spec.evidenceRelevant key) =
      events.filter (spec.evidenceRelevant key) := by
  by_cases selected : key = safetyDemands.identity .audit
  · subst key
    induction events with
    | nil => rfl
    | cons event events inductionHypothesis =>
        cases event <;> simp_all [expandEvent, spec, safetyDemands]
  · induction events with
    | nil => rfl
    | cons event events inductionHypothesis =>
        cases event <;> simp_all [expandEvent, spec, safetyDemands]

/-- Duplicate only internal audit work. Functional observations remain exact,
while an infinite concrete step may expand to two abstract steps. -/
def duplicateInternal : RefinementLens spec where
  project events := events.flatMap expandEvent
  project_nil := rfl
  project_append := fun _ _ => List.flatMap_append
  observationExact events := by
    induction events with
    | nil => rfl
    | cons event events inductionHypothesis =>
        change observations.project (List.flatMap expandEvent events) =
          observations.project events at inductionHypothesis
        cases event <;> simpa [observations, expandEvent] using inductionHypothesis
  evidenceNonErasing key events := by
    rw [expandEvent_preservesEvidence]
    exact List.Sublist.refl _

theorem duplicateInternal_prefix (length : Nat) :
    duplicateInternal.project (internalLoop.prefixEvents length) =
      List.replicate (length + length) Event.internal := by
  rw [internalLoop_prefixEvents]
  change List.flatMap expandEvent (List.replicate length Event.internal) = _
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      change [Event.internal, Event.internal] ++
          List.flatMap expandEvent (List.replicate length Event.internal) = _
      rw [inductionHypothesis]
      rw [show length + 1 + (length + 1) = (length + length) + 2 by omega]
      simp [List.replicate_succ]

theorem expandedPrefixEvents (length : Nat) :
    internalLoop.prefixEvents (length + length) =
      duplicateInternal.project (internalLoop.prefixEvents length) := by
  rw [internalLoop_prefixEvents, duplicateInternal_prefix]

theorem expandedCoverage (length : Nat) :
    (internalLoop.prefixEvents length).IsPrefix
      (duplicateInternal.project (internalLoop.prefixEvents length)) := by
  rw [duplicateInternal_prefix, internalLoop_prefixEvents]
  exact ⟨List.replicate length Event.internal, by simp⟩

/-- This witness exercises an abstract intermediate boundary between every two
abstract steps generated by one concrete step. -/
def expandedInfinite : InfiniteRefinement (concrete := loopBehavior)
    (abstract := loopBehavior) duplicateInternal (fun _ : Unit => ())
      (fun _ : Unit => ()) internalLoop where
  abstractExecution := internalLoop
  abstractPrefix length := ⟨length, expandedCoverage length⟩
  concreteBoundary length :=
    ⟨length + length, expandedPrefixEvents length, rfl, rfl⟩

example :
    (expandedInfinite.abstractExecution.prefixEvents 1).IsPrefix
      (duplicateInternal.project (internalLoop.prefixEvents 1)) :=
  by
    change (internalLoop.prefixEvents 1).IsPrefix
      (duplicateInternal.project (internalLoop.prefixEvents 1))
    exact expandedCoverage 1

end WeakSegmentRefinementFixture

example : artifactFormat.Parses (emitProgram verified) () :=
  emitProgram_parses verified

#audit_verified_programs

end Grass.Tests.Foundation
