import Grass.Refinement.Console.WriteFileConsoleHistory
import Tests.Platform.Win32WriteFileConsolePublication

/-! Concrete composition of the conditional quiet WriteFile history with static
console attribution.  The fixture's causal relation is stated explicitly; no
native WriteFile execution or general environment applicability is inferred. -/

namespace Grass.Tests.Console.WriteFileConsoleHistory

open Grass.Console Grass.Semantics Grass.Std.Logical Grass.Op
open Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Platform.Win32.WriteFile.ConsolePublication
open Grass.Refinement.Console.WriteFileHistory

open Grass.Tests.Win32WriteFileService

theorem handoffCausality : HandoffCausality Grass.Tests.Win32WriteFile.noEffects.causal call record
    Grass.Tests.Win32WriteFile.initial protocol₀ where
  beforeValid := Grass.Tests.Win32WriteFile.noEffects_valid Grass.Tests.Win32WriteFile.initial
  afterValid := Grass.Tests.Win32WriteFile.noEffects_valid protocol₀
  historyExtends := by intros _ _ h; exact False.elim h
  entry := List.mem_cons_self
  callerEntry := by intro old present; change old ∈ [] at present; contradiction

/-- The actual root of `receipt₁`: its full five-loan plan and exact handoff. -/
def handoffHistory : History runtime.loanPlan Grass.Tests.Win32WriteFile.noEffects Grass.Tests.Win32WriteFile.initial
    call record prefix₀ :=
  .handoff prefix₀ rfl Grass.Tests.Win32WriteFile.prepared handoffCausality rfl

def captured : Grass.SpecProcess Grass.ConsoleResourceModel.singleLine :=
  Grass.SpecProcess.ofRelational (Grass.Console.writeLineContract _ "\u000b\u0016!" ⟨true, false, false, false⟩)

def projection : CapturedTargetProjection captured Bool :=
  captured.project ⟨Grass.Specification.TextEncoding.utf8, ""⟩ id

theorem projection_payload_exact : projection.target.payload = Grass.Tests.Win32WriteFile.bytes := by decide

def startCut : OutputCut projection.target.payload := ⟨0, by decide⟩

def upper : projection.componentSystem.History :=
  Grass.Console.Behavior.pendingAt projection.target.payload startCut

def start : Start projection record where
  upper := upper
  cut := startCut
  located := Grass.Console.Behavior.pendingAt_state _ _
  suffix := by decide

/-- This relation selects only the concrete conditional handoff root used here. -/
def relation : HandoffRelation (plan := runtime.loanPlan) projection :=
  fun realization initial call record upper state frontier =>
    realization = Grass.Tests.Win32WriteFile.noEffects ∧ initial = Grass.Tests.Win32WriteFile.initial ∧
      call = Grass.Tests.Win32WriteFileService.call ∧
      record = Grass.Tests.Win32WriteFileService.record ∧
      upper = Grass.Tests.Console.WriteFileConsoleHistory.upper ∧ state = protocol₀ ∧
      HEq frontier prefix₀

def aligned : Aligned relation handoffHistory where
  start := start
  aligned := ⟨rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩

def extended? := aligned.extendConsole? receipt₁ Grass.Tests.Win32WriteFileConsolePublication.environment
  Grass.Tests.Win32WriteFileConsolePublication.observation

def extended := aligned.extend action (.fromList [])
  receipt₁.committed

theorem admitted_zero_step : extended? = some extended := by rfl

/-- The admitted zero publication retains the very same reached upper history. -/
theorem admitted_zero_retains_upper : extended.upper = aligned.upper := by
  exact Aligned.extendConsole?_zero admitted_zero_step rfl

def wrongRoute? := aligned.extendConsole? receipt₁
  Grass.Tests.Win32WriteFileConsolePublication.otherRouteEnvironment Grass.Tests.Win32WriteFileConsolePublication.otherRouteObservation

theorem wrong_route_general_match_still_true :
    ConsolePublication.matches? Grass.Tests.Win32WriteFileConsolePublication.otherRouteEnvironment
      receipt₁
        Grass.Tests.Win32WriteFileConsolePublication.otherRouteObservation = true := by decide

/-- General attribution succeeds, but the stdout-specific composition refuses. -/
theorem wrong_route_refused : wrongRoute?.isNone := by decide

end Grass.Tests.Console.WriteFileConsoleHistory
