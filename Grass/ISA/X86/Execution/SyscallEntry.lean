import Grass.ISA.X86.Execution.AccessFree
import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.RunFactory
import Grass.ISA.X86.LinearAddress

/-!
# Checked legacy 64-bit SYSCALL entry projection

The normal receipt retains the actual fetch and fixed access-free step, then
computes the tracked CPU and CPL/selector projection. Kernel service execution,
return, hidden segment caches, instruction ordering/serialization, and physical configuration correspondence are
separate obligations. No Windows or Linux syscall identity is selected here.

The bounded profile requires 64-bit mode, SCE, FRED disabled, CET disabled, and
incoming RF clear, and a ring-zero STAR selector. The RF restriction avoids conflating Intel's R11 := RFLAGS
pseudocode with AMD's explicit RF-cleared R11. Neither RF-set behavior nor
FRED/CET entry is supplied by this model.

Inspected authority: Intel SDM 092 Vol. 2B SYSCALL 4-698–4-700; AMD APM 24594
revision 3.38 SYSCALL 484–487. The successful checks below establish modeled
execution; declaration-level source enrollment and hardware applicability
remain separate.
-/

namespace Grass.ISA.X86.Execution.SyscallEntry
open Grass.Core Grass.Memory Grass.Op

/-- Mode and MSR inputs for the bounded normal entry profile. -/
structure Configuration where
  longMode : Bool
  code64 : Bool
  enabled : Bool
  fred : Bool
  callerShadowStack : Bool
  kernelShadowStack : Bool
  kernelIbt : Bool
  linearMode : LinearAddressMode
  lstar : BitVec 64
  star : BitVec 64
  flagsMask : BitVec 64

/-- `Admitted` checks the bounded common profile, including the RF-clear
restriction; failure of this predicate is not a physical fault classification. -/
def Admitted (config : Configuration) (before : State) : Prop :=
  config.longMode = true ∧ config.code64 = true ∧ config.enabled = true ∧
  config.fred = false ∧ config.callerShadowStack = false ∧
  config.kernelShadowStack = false ∧ config.kernelIbt = false ∧
  Canonical config.linearMode config.lstar ∧ before.rflags &&& resumeMask = 0 ∧
  (BitVec.extractLsb' 32 16 config.star &&& 3) = 0

instance (config : Configuration) (before : State) : Decidable (Admitted config before) := by
  unfold Admitted
  infer_instance

/-- Only the CPL and visible selector projection, not hidden segment state. -/
structure ControlProjection where
  cpl : BitVec 2
  cs : BitVec 16
  ss : BitVec 16

/-- The selector arithmetic uses the same supplied STAR value. -/
def control (config : Configuration) : ControlProjection :=
  let selector := BitVec.extractLsb' 32 16 config.star
  ⟨0, selector &&& 0xFFFC, selector + 8⟩

/-- An eligible actual fetched SYSCALL followed by the fixed no-data step. -/
structure Normal (config : Configuration) (before : State)
    (afterFetch afterEntry : MachineState) where
  execution : AccessFree before afterFetch afterEntry
  encoding : execution.fetch.site.encoding = SyscallEncoding.encoding
  admitted : Admitted config before

namespace Normal

/-- The visible privilege projection computed from this receipt's configuration. -/
def controlProjection {config before afterFetch afterEntry}
    (_receipt : Normal config before afterFetch afterEntry) : ControlProjection := control config

/-- `result` computes the tracked entry registers from the exact fetched site. -/
def result {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) : State :=
  { (before.withGpr .rcx receipt.execution.fetch.site.fallthroughRip).withGpr .r11 before.rflags with
    machine := afterEntry
    rip := config.lstar
    rflags := before.rflags &&& ~~~config.flagsMask }

theorem rcx_exact {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.gpr .rcx = receipt.execution.fetch.site.fallthroughRip := by
  simp [result, State.withGpr]

theorem r11_exact {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.gpr .r11 = before.rflags := by simp [result, State.withGpr]

theorem rip_exact {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.rip = config.lstar := rfl

theorem rflags_exact {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.rflags = before.rflags &&& ~~~config.flagsMask := rfl

theorem gpr_frame {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) (register : Gpr)
    (notRcx : register ≠ .rcx) (notR11 : register ≠ .r11) :
    receipt.result.gpr register = before.gpr register := by
  simp [result, State.withGpr, notRcx, notR11]

theorem rsp_exact {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.gpr .rsp = before.gpr .rsp := receipt.gpr_frame .rsp (by decide) (by decide)

theorem memory_frame {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.machine.memory = before.machine.memory := receipt.execution.state_frame.1

theorem obligations_frame {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.machine.obligations = before.machine.obligations := receipt.execution.state_frame.2

theorem events_frame {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) :
    receipt.result.machine.events = afterFetch.events := receipt.execution.events_frame

theorem cpl_exact {config before afterFetch afterEntry}
    (receipt : Normal config before afterFetch afterEntry) : receipt.controlProjection.cpl = 0 := rfl

end Normal

inductive Failure where
  | fetch (reason : FetchFactory.Failure)
  | unsupported (reached : State) (instruction : Instruction)
  | outsideProfile (reached : State)
  | operation (reached : State) (reason : StepRejection)

structure Success (policy : CpuAccessPolicy) (config : Configuration) (before : State) where
  fetched : FetchFactory.Success policy before
  afterEntry : MachineState
  receipt : Normal config before fetched.after afterEntry
  fetch_exact : receipt.execution.fetch = fetched.dispatched.fetch

/-- `fromFetched` checks the actual selection and profile before constructing
the normal receipt from the actual fixed operation result. -/
def fromFetched {policy : CpuAccessPolicy} (config : Configuration) (before : State)
    (fetched : FetchFactory.Success policy before) : Except Failure (Success policy config before) :=
  match selected : fetched.dispatched.selection.instruction with
  | .syscall =>
    if admitted : Admitted config before then
      let site := fetched.dispatched.fetch
      match RunFactory.accessFree site.run.policy fetched.after site.run.context
          site.run.contextKind site.run.cause with
      | .error reason => .error (.operation { before with machine := fetched.after } reason)
      | .ok computed =>
        .ok
          { fetched := fetched
            afterEntry := computed.1
            receipt :=
              { execution :=
                  { fetch := site, operation := RunFactory.accessFreeOperation,
                    sequence := .none_, selected := rfl, noDataSubsteps := rfl,
                    faultAt := RunFactory.noFaultPlan, noFault := rfl, ran := computed.2.ran }
                encoding := by
                  have exact := fetched.dispatched.selection.encoding_eq
                  rw [selected] at exact
                  exact (Option.some.inj exact).symm
                admitted := admitted }
            fetch_exact := rfl }
    else .error (.outsideProfile { before with machine := fetched.after })
  | instruction => .error (.unsupported { before with machine := fetched.after } instruction)

/-- `enter` obtains its own actual fetch before invoking `fromFetched`. -/
def enter (policy : CpuAccessPolicy) (config : Configuration) (before : State) :
    Except Failure (Success policy config before) :=
  match FetchFactory.fetch policy before with
  | .error reason => .error (.fetch reason)
  | .ok fetched => fromFetched config before fetched

end Grass.ISA.X86.Execution.SyscallEntry
