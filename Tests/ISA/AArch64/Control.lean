import Grass.ISA.AArch64.Source
import Grass.ISA.AArch64.Sources

/-! Discriminating body/encoding fixtures. No hardware or full-machine claims. -/
namespace Tests.ISA.AArch64

open Grass.ISA.AArch64 Grass.Std.Logical

private def highOnly : Cpu := ⟨fun _ => 0x100000000, 0x1000, 0b1010⟩
private def forward32 : CompareZero := ⟨0, 2, 0⟩
private def forward64 : CompareZero := ⟨1, 2, 0⟩

-- W reads ignore high X bits, whereas X reads observe them.
example : (forward32.execute highOnly).pc = 0x1008 := by decide
example : (forward64.execute highOnly).pc = 0x1004 := by decide
example : (forward32.execute highOnly).nzcv = 0b1010 := by decide
example : (forward32.execute highOnly).gpr ⟨0, by decide⟩ = 0x100000000 := by decide

-- Rt=31 reads ZR independently of the register file. Displacement is signed.
example : (CompareZero.mk 1 0x7ffff 31).isZero highOnly = true := by decide
example : ((CompareZero.mk 1 0x7ffff 31).execute highOnly).pc = 0xffc := by decide
example : (CompareZero.mk 1 0x40000 0).offset = 0xfffffffffff00000 := by decide
example : (CompareZero.mk 1 0x3ffff 0).offset = 0xffffc := by decide
example : ((CompareZero.mk 1 1 31).execute { highOnly with pc := 0xfffffffffffffffc }).pc = 0 := by
  decide

-- Fixed independently readable opcode examples and neighboring-family rejection.
example : forward64.encode = 0xb4000040 := by decide
example : (CompareZero.mk 0 0x7ffff 1).encode = 0x34ffffe1 := by decide
example : CompareZero.decode 0x35000000 = none := by decide -- CBNZ W0
example : CompareZero.decode 0x14000000 = none := by decide -- B
example : CompareZero.decode 0xd4000001 = none := by decide -- SVC
example : SupervisorCall.encode 0 = 0xd4000001 := by decide
example : SupervisorCall.encode 0xffff = 0xd41fffe1 := by decide
example : SupervisorCall.decode 0xd4000002 = none := by decide -- HVC
example : SupervisorCall.decode 0xd4000003 = none := by decide -- SMC
example : SupervisorCall.decode 0xd4200000 = none := by decide -- BRK

example : (emitWord forward64.encode).toList = [0x40, 0, 0, 0xb4] := by decide
example : (emitWord (SupervisorCall.encode 0)).toList = [1, 0, 0, 0xd4] := by decide
example : Grass.Artifact.Binary.takeLittleEndian 4 (Vec.fromList [1, 0, 0, 0xd4, 0xaa]) =
    .done 0xd4000001 (Vec.fromList [0xaa]) := by rfl
example : readSource (Vec.fromList [1, 0, 0]) = .needMore (some 1) := by
  apply readSource_needMore
  rfl

-- A receipt exposes precisely the indexed CPU, including nonzero syscall numbers.
private def request : SupervisorCall.Request (SupervisorCall.encode 0) highOnly :=
  ⟨0, SupervisorCall.decode_encode 0⟩
example : request.register ⟨8, by decide⟩ = 0x100000000 := by decide

-- Source connection is universally quantified, rather than a selected test run.
example (instruction : CompareZero) (cpu : Cpu) :
    BodyStep instruction.encode cpu (.next (instruction.execute cpu)) :=
  (instruction.sourceStep cpu).step

#print axioms Grass.ISA.AArch64.CompareZero.decode_encode
#print axioms Grass.ISA.AArch64.SupervisorCall.decode_encode
#print axioms Grass.ISA.AArch64.bodyStep_cases
#print axioms Grass.ISA.AArch64.SourceBodyStep.cases
#print axioms Grass.ISA.AArch64.CompareZero.sourceStep
#print axioms Grass.ISA.AArch64.SupervisorCall.sourceStep
#print axioms Grass.ISA.AArch64.SupervisorCall.Request.source_exact
#print axioms Grass.ISA.AArch64.readSource_needMore
#print axioms Grass.ISA.AArch64.citations_checked

end Tests.ISA.AArch64
