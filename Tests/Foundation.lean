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
  InfiniteConsistent := fun _ _ _ _ => True
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

example : True :=
  (initialExecution true).runs.inductionOn
    (motive := fun _ => True)
    (fun _ => trivial)
    (fun _ _ _ => trivial)

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
    (initialExecution true).state (initialExecution true).graph) :=
  verified.execution_completes (initialExecution true)

example : artifactFormat.Parses (emitProgram verified) () :=
  emitProgram_parses verified

#audit_verified_programs

end Grass.Tests.Foundation
