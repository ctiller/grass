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
  terminalNoStep _ := fun {_ _ _ _} transition => False.elim transition

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

example (refinement : BehaviorRefinement behavior behavior) :
    (BehaviorRefinement.refl behavior).trans refinement = refinement := by simp

example (refinement : BehaviorRefinement behavior behavior) :
    refinement.trans (BehaviorRefinement.refl behavior) = refinement := by simp

example (first second third : BehaviorRefinement behavior behavior) :
    (first.trans second).trans third = first.trans (second.trans third) := by simp

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
  terminalNoStep terminal := False.elim terminal

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
  terminalNoStep terminal := False.elim terminal

abbrev abstractBehavior : ProgramBehavior spec where
  system := abstractSystem
  inputOf := fun _ => false

def toAbstract : BehaviorRefinement behavior abstractBehavior where
  mapState := fun _ => false
  mapGraph := fun _ => 0
  mapChoice := fun _ => 0
  input := fun _ => rfl
  initial := fun _ => trivial
  step := fun _ => trivial
  terminal := fun terminal => False.elim terminal
  infiniteConsistency := fun _ => trivial

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
  terminalNoStep terminal := False.elim terminal

abbrev highestBehavior : ProgramBehavior spec where
  system := highestSystem
  inputOf := fun _ => false

def toHighest : BehaviorRefinement abstractBehavior highestBehavior where
  mapState := Bool.toNat
  mapGraph := fun _ => true
  mapChoice := fun _ => false
  input := fun _ => rfl
  initial := fun _ => trivial
  step := fun _ => trivial
  terminal := fun terminal => False.elim terminal
  infiniteConsistency := fun _ => trivial

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
    (toAbstract.mapPrefix emptyPrefix).step (toAbstract.step firstStep) := by
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

example : (toAbstract.mapPrefix samplePrefix).events = samplePrefix.events :=
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
  terminalNoStep terminal := False.elim terminal

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

example : (BehaviorRefinement.refl behavior).mapInfinite continuation = continuation :=
  BehaviorRefinement.mapInfinite_refl behavior continuation

example : (toAbstract.trans toHighest).mapInfinite continuation =
    toHighest.mapInfinite (toAbstract.mapInfinite continuation) :=
  BehaviorRefinement.mapInfinite_trans toAbstract toHighest continuation

example : (BehaviorRefinement.refl behavior).mapCompletion completion = completion :=
  BehaviorRefinement.mapCompletion_refl behavior completion

example : (toAbstract.trans toHighest).mapCompletion completion =
    toHighest.mapCompletion (toAbstract.mapCompletion completion) :=
  BehaviorRefinement.mapCompletion_trans toAbstract toHighest completion

example : (BehaviorRefinement.refl behavior).mapCompletionAtPrefix
    samplePrefix completion = completion :=
  BehaviorRefinement.mapCompletionAtPrefix_refl behavior samplePrefix completion

example : (toAbstract.trans toHighest).mapCompletionAtPrefix
    samplePrefix completion =
    toHighest.mapCompletionAtPrefix (toAbstract.mapPrefix samplePrefix)
      (toAbstract.mapCompletionAtPrefix samplePrefix completion) :=
  BehaviorRefinement.mapCompletionAtPrefix_trans
    toAbstract toHighest samplePrefix completion

def mappedCompletion : abstractBehavior.system.Completion
    (toAbstract.mapPrefix samplePrefix).state
    (toAbstract.mapPrefix samplePrefix).graph
    (toAbstract.mapPrefix samplePrefix).events :=
  toAbstract.mapCompletionAtPrefix samplePrefix completion

example : samplePrefix.events = [true] := rfl

end InfinitePrefixFixture

example : artifactFormat.Parses (emitProgram verified) () :=
  emitProgram_parses verified

#audit_verified_programs

end Grass.Tests.Foundation
