import Grass.ISA.X86.Execution.State

/-! Full RFLAGS transfer for ordinary completed PUSH/SUB, before event delivery.

The instruction entries alone do not describe RF. Intel SDM 092 Vol. 3B
§20.3.1.1 pp. 20-9–20-10 and AMD APM Vol. 2 (24593 rev. 3.45) §3.1.6 p. 55
both require RF clear on ordinary successful completion. PUSH has no additional
flag changes; SUB writes six status flags (Intel Vol. 2B PUSH/SUB entries;
AMD Vol. 3 rev. 3.38 pp. 297–298 and 356–357).

These functions do not execute an instruction, certify completion, or describe
the RFLAGS image saved by fault/trap/interrupt delivery. Exact completed-step
evidence and the bounded profile are obligations of the execution adapter.
-/
namespace Grass.ISA.X86.Execution

open RegisterSemantics

/-- RF, distinct from the six arithmetic status bits. -/
def resumeMask : BitVec 64 := 0x10000

/-- Removing RF changes none of the existing six status-flag projections. -/
theorem statusFlags_clearResume (bits : BitVec 64) :
    Flags.fromBits (bits &&& ~~~resumeMask) = Flags.fromBits bits := by
  simp [Flags.fromBits, resumeMask]

/-- Full flags after ordinary completed PUSH, before any event delivery. -/
def completedPushRflags (state : State) : BitVec 64 := state.rflags &&& ~~~resumeMask

theorem completedPushRflags_status (state : State) :
    Flags.fromBits (completedPushRflags state) = state.statusFlags :=
  statusFlags_clearResume state.rflags

theorem completedPushRflags_resume (state : State) :
    (completedPushRflags state).getLsbD 16 = false := by
  simp [completedPushRflags, resumeMask]

/-- SUB defines all six status flags. The following exactness theorem justifies
the projection from Option; this is not an arbitrary representative of undefined flags. -/
def completedSubStatus (state : State) (immediate : ImmediateArithmetic.Immediate) :
    Flags Bool :=
  (evaluateImmediate .sub .w64 (state.gpr .rsp) immediate state.statusFlags).flags.map
    (·.getD false)

private theorem restoreDefined (cf pf af zf sf of : Bool) :
    ((⟨some cf, some pf, some af, some zf, some sf, some of⟩ : Flags (Option Bool)).map
      (·.getD false)).map some = ⟨some cf, some pf, some af, some zf, some sf, some of⟩ := rfl

theorem completedSubStatus_exact (state : State) (immediate : ImmediateArithmetic.Immediate) :
    (completedSubStatus state immediate).map some =
      (evaluateImmediate .sub .w64 (state.gpr .rsp) immediate state.statusFlags).flags :=
  restoreDefined _ _ _ _ _ _

/-- Merge the six defined SUB flags and independently clear RF. This retains
the other full-RFLAGS bits instead of serializing only a six-bit projection. -/
def completedSubRflags (state : State) (immediate : ImmediateArithmetic.Immediate) :
    BitVec 64 :=
  (state.withStatusFlags (completedSubStatus state immediate)).rflags &&& ~~~resumeMask

theorem completedSubRflags_status (state : State) (immediate : ImmediateArithmetic.Immediate) :
    Flags.fromBits (completedSubRflags state immediate) = completedSubStatus state immediate := by
  rw [completedSubRflags, statusFlags_clearResume]
  exact state.withStatusFlags_statusFlags _

theorem completedSubRflags_resume (state : State) (immediate : ImmediateArithmetic.Immediate) :
    (completedSubRflags state immediate).getLsbD 16 = false := by
  simp [completedSubRflags, resumeMask]

end Grass.ISA.X86.Execution
