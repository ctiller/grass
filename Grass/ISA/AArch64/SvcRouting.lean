import Grass.ISA.AArch64.Control

/-!
Deterministic SVC routing projection for explicit non-secure, non-VHE A64 EL0
configuration. This evaluates routing only: a plan is NOT exception entry or
eligibility for a completed machine transition. SSAdvance, saved PSTATE, debug,
error synchronization, transaction failure and TakeException remain unresolved.
No fetch, fault alternative or memory event is consumed or erased here.

Authority: DDI 0602 ID032025, printed pp.5400, 5410, 5970, 5972.
-/
namespace Grass.ISA.AArch64.SupervisorCall.Routing

inductive ExecutionState where
  | a64 | a32
deriving DecidableEq, Repr

inductive Security where
  | nonSecure | secure | realm | root
deriving DecidableEq, Repr

/-- Named architectural fields, not a caller-supplied effective routing answer. -/
structure El2 where
  execution : ExecutionState
  hcrTge : Bool
  hfgitrSvcEl0 : Bool
deriving DecidableEq, Repr

structure El3 where
  execution : ExecutionState
  scrNS : Bool
  scrFGTEn : Bool
deriving DecidableEq, Repr

/-- Explicit projection of the input machine configuration. No field defaults.
Other architectural features are outside this routing projection, not absent.
`none` declares that an exception level is not implemented. This declaration
still needs to be tied to the actual predecessor by a machine consumer. -/
structure Configuration where
  currentEL : BitVec 2
  currentExecution : ExecutionState
  el1Execution : ExecutionState
  security : Security
  featVHE : Bool
  featRME : Bool
  featFGT : Bool
  el2 : Option El2
  el3 : Option El3
deriving DecidableEq, Repr

inductive Unsupported where
  | currentEL | currentExecution | el1Execution | security
  | vhe | rme | el2Execution | el3Execution | securityControl
deriving DecidableEq, Repr

/-- Once the supported regime is checked, these are computed from input fields.
In this non-secure regime EL2Enabled is exactly presence of EL2. Without VHE,
IsInHost is false. Neither predicate is accepted as an opaque favorable input. -/
structure Controls where
  fgtIntercept : Bool
  tgeRoute : Bool
deriving DecidableEq, Repr

def check (config : Configuration) : Except Unsupported Controls := do
  if config.currentEL != 0 then throw .currentEL
  if config.currentExecution != .a64 then throw .currentExecution
  if config.el1Execution != .a64 then throw .el1Execution
  if config.security != .nonSecure then throw .security
  if config.featVHE then throw .vhe
  if config.featRME then throw .rme
  let fgtEnabled ← match config.el3 with
    | none => pure true
    | some el3 => do
      if el3.execution != .a64 then throw .el3Execution
      if !el3.scrNS then throw .securityControl
      pure el3.scrFGTEn
  match config.el2 with
  | none => pure ⟨false, false⟩
  | some el2 => do
    if el2.execution != .a64 then throw .el2Execution
    pure ⟨config.featFGT && el2.hfgitrSvcEl0 && fgtEnabled, el2.hcrTge⟩

inductive Route where
  | el1 | el2FGT | el2TGE
deriving DecidableEq, Repr

/-- CheckForSVCTrap has priority over CallSupervisor's ordinary TGE routing. -/
def select (controls : Controls) : Route :=
  if controls.fgtIntercept then .el2FGT
  else if controls.tgeRoute then .el2TGE else .el1

theorem select_el1_iff (controls : Controls) :
    select controls = .el1 ↔
      controls.fgtIntercept = false ∧ controls.tgeRoute = false := by
  cases controls with
  | mk fgt tge => cases fgt <;> cases tge <;> decide

theorem fgt_priority (tge : Bool) : select ⟨true, tge⟩ = .el2FGT := rfl

/-- Preferred return address passed to TakeException, not an installed ELR. -/
def Route.preferredReturn (route : Route) (cpu : Cpu) : BitVec 64 :=
  match route with
  | .el2FGT => cpu.pc
  | .el1 | .el2TGE => cpu.pc + 4

/-- Every successful assessment retains its exact checked configuration and
source request. This is a routing plan, with no successor machine or event. -/
structure Plan (config : Configuration) (word : BitVec 32) (cpu : Cpu) where
  request : Request word cpu
  controls : Controls
  checked : check config = .ok controls

def Plan.route {config : Configuration} {word : BitVec 32} {cpu : Cpu}
    (plan : Plan config word cpu) : Route := select plan.controls

def Plan.preferredReturn {config : Configuration} {word : BitVec 32} {cpu : Cpu}
    (plan : Plan config word cpu) : BitVec 64 := plan.route.preferredReturn cpu

def assess (config : Configuration) {word : BitVec 32} {cpu : Cpu}
    (request : Request word cpu) : Except Unsupported (Plan config word cpu) :=
  match checked : check config with
  | .error reason => .error reason
  | .ok controls => .ok ⟨request, controls, checked⟩

theorem assess_refused (config : Configuration) {word : BitVec 32} {cpu : Cpu}
    (request : Request word cpu) (reason : Unsupported)
    (rejected : check config = .error reason) : assess config request = .error reason := by
  unfold assess
  split
  next reason' checked => simp_all
  next controls checked => rw [rejected] at checked; contradiction

theorem Plan.el1_iff {config : Configuration} {word : BitVec 32} {cpu : Cpu}
    (plan : Plan config word cpu) :
    plan.route = .el1 ↔
      plan.controls.fgtIntercept = false ∧ plan.controls.tgeRoute = false :=
  select_el1_iff plan.controls

theorem Plan.source_exact {config : Configuration} {word : BitVec 32} {cpu : Cpu}
    (plan : Plan config word cpu) : encode plan.request.immediate = word :=
  plan.request.source_exact

end Grass.ISA.AArch64.SupervisorCall.Routing
