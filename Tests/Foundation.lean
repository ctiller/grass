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

def noDerivedDemands : DerivedDemandFamily noDemands.identities where
  demands := noDemands
  origin := fun key => nomatch key
  fresh := fun derived => nomatch derived

def spec : SpecProcess where
  Input := Bool
  AuditEvent := Bool
  Observation := Bool
  admits := fun _ => True
  observationProjection := .identity Bool
  accepts := fun _ _ => True
  requirements := noDemands

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

example : Nonempty { execution :
    (artifactFormat.loadedBehavior ByteArray.empty).system.ExecutionPrefix //
    (artifactFormat.loadedBehavior ByteArray.empty).HasInput true execution } :=
  verified.execution_nonempty true trivial

example : Nonempty ((artifactFormat.loadedBehavior ByteArray.empty).system.Completion
    (initialExecution true).state (initialExecution true).graph
      (initialExecution true).events) :=
  verified.execution_completes (initialExecution true)

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

def samplePrefix : system.ExecutionPrefix :=
  RelationalSystem.ExecutionPrefix.step
    (RelationalSystem.ExecutionPrefix.initial (system := system)
      (state := ()) (graph := ()) trivial)
    (choice := ()) (event := true) (nextState := ()) (nextGraph := ()) trivial

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

def completion : system.Completion samplePrefix.state samplePrefix.graph samplePrefix.events :=
  .infinite continuation

example : samplePrefix.events = [true] := rfl

end InfinitePrefixFixture

example : artifactFormat.Parses (emitProgram verified) () :=
  emitProgram_parses verified

#audit_verified_programs

end Grass.Tests.Foundation
