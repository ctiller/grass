import Grass.ISA.AArch64.SvcRouting

namespace Tests.ISA.AArch64.SvcRouting
open Grass.ISA.AArch64 SupervisorCall.Routing

private def base : Configuration :=
  ⟨0, .a64, .a64, .nonSecure, false, false, true,
    some ⟨.a64, false, true⟩, some ⟨.a64, true, true⟩⟩

-- FGT is gated by feature presence and EL3 enable, not merely its trap bit.
example : check base = .ok ⟨true, false⟩ := by rfl
example : check { base with featFGT := false } = .ok ⟨false, false⟩ := by rfl
example : check { base with el3 := some ⟨.a64, true, false⟩ } =
    .ok ⟨false, false⟩ := by rfl
example : check { base with el3 := none } = .ok ⟨true, false⟩ := by rfl
example : check { base with el2 := none } = .ok ⟨false, false⟩ := by rfl
example : check { base with el2 := some ⟨.a64, true, true⟩ } =
    .ok ⟨true, true⟩ := by rfl
example : select ⟨true, true⟩ = .el2FGT := by rfl
example : select ⟨false, true⟩ = .el2TGE := by rfl
example : select ⟨false, false⟩ = .el1 := by rfl

-- Unsupported regimes are not silently interpreted as the selected profile.
example : check { base with featVHE := true } = .error .vhe := by rfl
example : check { base with featRME := true } = .error .rme := by rfl
example : check { base with security := .secure } = .error .security := by rfl
example : check { base with currentEL := 1 } = .error .currentEL := by rfl
example : check { base with currentExecution := .a32 } =
    .error .currentExecution := by rfl
example : check { base with el1Execution := .a32 } = .error .el1Execution := by rfl
example : check { base with el2 := some ⟨.a32, true, true⟩ } =
    .error .el2Execution := by rfl
example : check { base with el3 := some ⟨.a32, true, true⟩ } =
    .error .el3Execution := by rfl
example : check { base with el3 := some ⟨.a64, false, true⟩ } =
    .error .securityControl := by rfl

private def cpu : Cpu := ⟨fun _ => 0x1234, 0xfffffffffffffffc, 0⟩
private def request : SupervisorCall.Request (SupervisorCall.encode 7) cpu :=
  ⟨7, SupervisorCall.decode_encode 7⟩
private def plan : Plan base (SupervisorCall.encode 7) cpu :=
  ⟨request, ⟨true, false⟩, by rfl⟩
example : plan.preferredReturn = 0xfffffffffffffffc := by rfl
example : Route.preferredReturn .el2TGE cpu = 0 := by rfl
example : Route.preferredReturn .el1 cpu = 0 := by rfl
example : plan.request.register ⟨8, by decide⟩ = 0x1234 := by rfl

#print axioms select_el1_iff
#print axioms fgt_priority
#print axioms assess_refused
#print axioms Plan.el1_iff
#print axioms Plan.source_exact
end Tests.ISA.AArch64.SvcRouting

