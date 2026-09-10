import Grass.Target.Platform
import Grass.Certificate

/-!
# The generic machine tier

One `RelationalSystem` for every ISA and platform. A state is the ISA state
plus the platform environment and a phase: running, awaiting a platform
response, or halted. Steps are

- an internal ISA step, event `silent`;
- an ISA native call the platform decodes to a non-terminal request, event
  `call r`, moving to `awaiting`;
- an ISA native call the platform decodes to a terminal request (an exit),
  event `call r`, moving to `halted`: no response is ever delivered;
- the environment answering a pending request, event `reply r ρ`, chosen by
  the environment under `Platform.Responds`, resuming the ISA with the encoded
  return;
- an ISA halt, event `silent`.

A fault, an undecodable native call, and a request with no allowed response
are stuck states: no transition and not terminal. `Adequate.completion` for
this system therefore requires that no reachable state is stuck, which is
exactly control and memory safety plus platform-call well-formedness. That is
the obligation the assembly verifier discharges per program; this module only
makes it precise and target-independent.

The event type is `Service.Event D`. To be a `ProgramBehavior spec` the
events must be relabeled into `spec.AuditEvent`; `behavior` takes that map and
the input projection.
-/

namespace Grass.Target

open Grass.Service

namespace Machine

variable {isa : ISA} {D : Domain}

/-- Where the machine is between steps. -/
inductive Phase (isa : ISA) (D : Domain) : Type
  | running (state : isa.State)
  | awaiting (call : isa.NativeCall) (request : D.Request) (resume : isa.NativeReturn → isa.State)
  | halted

/-- The whole state of the generic machine. -/
structure State (isa : ISA) (D : Domain) (platform : Platform isa D) where
  /-- The environment the program was started in; fixed for the run so the
  specification input can be read from it. -/
  initialEnvironment : platform.Environment
  environment : platform.Environment
  phase : Phase isa D

/-- The environment's choice when answering a request. -/
inductive Choice (D : Domain) : Type
  | machine
  | respond (request : D.Request) (response : D.Response request)

variable (platform : Platform isa D)

/-- One transition. -/
inductive Step : State isa D platform → Choice D → Event D → State isa D platform → Prop
  | internal {state next : isa.State} {env0 env : platform.Environment}
      (step : isa.step state = .internal next) :
      Step ⟨env0, env, .running state⟩ .machine .silent ⟨env0, env, .running next⟩
  | halt {state : isa.State} {env0 env : platform.Environment}
      (step : isa.step state = .halted) :
      Step ⟨env0, env, .running state⟩ .machine .silent ⟨env0, env, .halted⟩
  | call {state : isa.State} {call : isa.NativeCall} {resume : isa.NativeReturn → isa.State}
      {request : D.Request} {env0 env : platform.Environment}
      (step : isa.step state = .external call resume)
      (decoded : platform.decode call = some request)
      (continues : ¬ D.Terminal request) :
      Step ⟨env0, env, .running state⟩ .machine (.call request)
        ⟨env0, env, .awaiting call request resume⟩
  | exit {state : isa.State} {call : isa.NativeCall} {resume : isa.NativeReturn → isa.State}
      {request : D.Request} {env0 env : platform.Environment}
      (step : isa.step state = .external call resume)
      (decoded : platform.decode call = some request)
      (ends : D.Terminal request) :
      Step ⟨env0, env, .running state⟩ .machine (.call request) ⟨env0, env, .halted⟩
  | reply {call : isa.NativeCall} {request : D.Request} {resume : isa.NativeReturn → isa.State}
      {response : D.Response request} {env0 env env' : platform.Environment}
      (allowed : platform.Responds env request response env') :
      Step ⟨env0, env, .awaiting call request resume⟩ (.respond request response)
        (.reply request response)
        ⟨env0, env', .running (resume (platform.encodeReturn call request response))⟩

/-- The generic machine as a relational system. Graphs are trivial: the
machine has no causal structure beyond its trace. -/
def system (raw : isa.Raw) : RelationalSystem (Event D) where
  State := State isa D platform
  Choice := Choice D
  Graph := Unit
  Initial state _ := platform.Admits state.initialEnvironment ∧
    state.environment = state.initialEnvironment ∧
    state.phase = .running (isa.initial raw (platform.entry state.initialEnvironment))
  Step _ state choice event next _ := Step platform state choice event next
  Terminal state _ := state.phase = .halted
  InfiniteConsistent _ _ _ _ _ := True
  Extends _ _ := True
  extendsRefl _ := trivial
  extendsTrans _ _ := trivial
  stepExtends _ := trivial

/-- A state with no transition and no terminal status. Reachability of such a
state is what the adequacy obligation excludes. -/
def Stuck (state : State isa D platform) : Prop :=
  state.phase ≠ .halted ∧ ∀ choice event next, ¬ Step platform state choice event next

/-- A running state whose ISA step faults is stuck. -/
theorem stuck_of_fault {state : isa.State} {env0 env : platform.Environment}
    {reason : isa.Fault} (faulted : isa.step state = .fault reason) :
    Stuck platform ⟨env0, env, .running state⟩ := by
  refine ⟨by simp, ?_⟩
  intro choice event next step
  cases step with
  | internal step' => rw [faulted] at step'; cases step'
  | halt step' => rw [faulted] at step'; cases step'
  | call step' _ _ => rw [faulted] at step'; cases step'
  | exit step' _ _ => rw [faulted] at step'; cases step'

/-- A running state whose native call the platform does not realize is stuck. -/
theorem stuck_of_undecoded {state : isa.State} {env0 env : platform.Environment}
    {call : isa.NativeCall} {resume : isa.NativeReturn → isa.State}
    (external : isa.step state = .external call resume)
    (undecoded : platform.decode call = none) :
    Stuck platform ⟨env0, env, .running state⟩ := by
  refine ⟨by simp, ?_⟩
  intro choice event next step
  cases step with
  | internal step' => rw [external] at step'; cases step'
  | halt step' => rw [external] at step'; cases step'
  | call step' decoded _ =>
      rw [external] at step'
      cases step'
      rw [undecoded] at decoded
      cases decoded
  | exit step' decoded _ =>
      rw [external] at step'
      cases step'
      rw [undecoded] at decoded
      cases decoded

/-- An awaiting state whose request the environment never answers is stuck. -/
theorem stuck_of_unanswered {call : isa.NativeCall} {request : D.Request}
    {resume : isa.NativeReturn → isa.State} {env0 env : platform.Environment}
    (unanswered : ∀ response env', ¬ platform.Responds env request response env') :
    Stuck platform ⟨env0, env, .awaiting call request resume⟩ := by
  refine ⟨by simp, ?_⟩
  intro choice event next step
  cases step with
  | reply allowed => exact unanswered _ _ allowed

/-- The behavior of a loaded program for a specification whose audit events
are a relabeling of the service events. -/
def behavior (raw : isa.Raw) (spec : SpecRoot)
    (eventOf : Event D → spec.AuditEvent)
    (inputOf : platform.Environment → spec.Input) : ProgramBehavior spec where
  system :=
    let base := system platform raw
    { State := base.State
      Choice := base.Choice
      Graph := base.Graph
      Initial := base.Initial
      Step := fun graph state choice event next graph' =>
        ∃ raw, base.Step graph state choice raw next graph' ∧ eventOf raw = event
      Terminal := base.Terminal
      InfiniteConsistent := fun _ _ _ _ _ => True
      Extends := base.Extends
      extendsRefl := base.extendsRefl
      extendsTrans := base.extendsTrans
      stepExtends := fun _ => trivial }
  inputOf state := inputOf state.initialEnvironment

end Machine

end Grass.Target
