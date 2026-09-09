import Grass.ISA.X86.RegisterSemantics
import Grass.Memory.State

/-!
# Architectural x86 execution representation

This is a carrier for the architectural state needed by an eventual x86
execution relation.  It deliberately contains the existing memory machine state
once, rather than copies of its memory, history, or fault ledgers.  Likewise,
`rflags` is the sole stored flags representation; `statusFlags` is a view of its
six status bits.

This module is a representation layer only.  In particular, `withStatusFlags`
is a pure masked replacement helper, not an instruction-transfer rule.
-/

namespace Grass.ISA.X86.Execution

open Grass.ISA.X86

/-- The architectural state threaded by a future x86 execution relation. -/
structure State where
  /-- The single authority for memory, events, faults, and their ledgers. -/
  machine : Grass.Memory.MachineState
  /-- The 64-bit general-purpose register file. -/
  gpr : Gpr → BitVec 64
  /-- The instruction pointer representation. -/
  rip : BitVec 64
  /-- The complete RFLAGS representation, including bits outside status flags. -/
  rflags : BitVec 64

/-- Read the six modeled status bits from the complete RFLAGS representation. -/
def State.statusFlags (state : State) : RegisterSemantics.Flags Bool :=
  RegisterSemantics.Flags.fromBits state.rflags

/-- Replace one GPR while framing the rest of the architectural representation. -/
def State.withGpr (state : State) (register : Gpr) (value : BitVec 64) : State :=
  { state with gpr := fun observed =>
      if observed = register then value else state.gpr observed }

@[simp] theorem State.withGpr_machine (state : State) (register : Gpr) (value : BitVec 64) :
    (state.withGpr register value).machine = state.machine := rfl

@[simp] theorem State.withGpr_rip (state : State) (register : Gpr) (value : BitVec 64) :
    (state.withGpr register value).rip = state.rip := rfl

@[simp] theorem State.withGpr_rflags (state : State) (register : Gpr) (value : BitVec 64) :
    (state.withGpr register value).rflags = state.rflags := rfl

@[simp] theorem State.withGpr_same (state : State) (register : Gpr) (value : BitVec 64) :
    (state.withGpr register value).gpr register = value := by
  simp [State.withGpr]

theorem State.withGpr_other (state : State) (written observed : Gpr) (value : BitVec 64)
    (h : observed ≠ written) :
    (state.withGpr written value).gpr observed = state.gpr observed := by
  simp [State.withGpr, h]

/-- The bit positions represented by `RegisterSemantics.Flags`. -/
def statusMask : BitVec 64 := 0x8D5

/--
Replace only the six modeled status bits in `rflags`.

This helper preserves the representation of every bit outside `statusMask`,
including RF, IF, and DF. `State.withStatusFlags` is a representation helper;
instruction-specific RFLAGS effects remain separate obligations.
-/
def State.withStatusFlags (state : State) (flags : RegisterSemantics.Flags Bool) : State :=
  { state with rflags := (state.rflags &&& ~~~statusMask) ||| flags.bits }

@[simp] theorem State.withStatusFlags_machine (state : State)
    (flags : RegisterSemantics.Flags Bool) :
    (state.withStatusFlags flags).machine = state.machine := rfl

@[simp] theorem State.withStatusFlags_gpr (state : State)
    (flags : RegisterSemantics.Flags Bool) :
    (state.withStatusFlags flags).gpr = state.gpr := rfl

@[simp] theorem State.withStatusFlags_rip (state : State)
    (flags : RegisterSemantics.Flags Bool) :
    (state.withStatusFlags flags).rip = state.rip := rfl

/-- The complete RFLAGS result is the declared masked merge. -/
@[simp] theorem State.withStatusFlags_rflags (state : State)
    (flags : RegisterSemantics.Flags Bool) :
    (state.withStatusFlags flags).rflags =
      (state.rflags &&& ~~~statusMask) ||| flags.bits := rfl

theorem State.withStatusFlags_statusFlags (state : State)
    (flags : RegisterSemantics.Flags Bool) :
    (state.withStatusFlags flags).statusFlags = flags := by
  cases flags
  rename_i cf pf af zf sf of
  cases cf <;> cases pf <;> cases af <;> cases zf <;> cases sf <;> cases of <;>
    simp [State.statusFlags, State.withStatusFlags, statusMask,
      RegisterSemantics.Flags.fromBits, RegisterSemantics.Flags.bits]

end Grass.ISA.X86.Execution
