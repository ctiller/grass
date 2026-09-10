import Grass.Service.Domain

/-!
# The ISA seam

An `ISA` is what a machine-code target must supply to participate in the
generic machine tier (`Grass.Target.Machine`) and the generic artifact tier
(`Grass.Target.Artifact`). It is the whole contract: nothing above it may
mention x86, AArch64, or Wasm, and nothing below it may mention a platform, a
service domain, or a program.

The interface is deliberately operational and small:

- `Instr` with a canonical `encode`/`decode` pair and the round-trip law;
- `Raw`, the assembled program an artifact writer serializes (sectioned bytes
  | instr :: rest => isa.encode instr ++ encodeAll restfor native targets, a module for Wasm);
- `State`, the whole machine state including memory;
- `step`, one instruction: an internal transition, a native call to the
  platform, a halt, or a fault.

Native calls are ISA-level: they carry the register/stack/memory view the
platform needs to decode a portable `Service` request (`NativeCall`) and the
machine-level effect of the platform's answer (`NativeReturn`: result
registers and memory writes). The ISA does not know what the call means.

Memory safety is not hidden in the ISA: an access outside the loaded image or
against its permissions is a `fault`, which makes the machine stuck, which
makes the machine tier's adequacy obligation unprovable. Proving adequacy is
therefore proving the absence of faults on every reachable state.
-/

namespace Grass.Target

/-- What one instruction did. -/
inductive StepOutcome (State NativeCall NativeReturn Fault : Type) : Type
  /-- An internal transition with no externally visible effect. -/
  | internal (next : State)
  /-- Control transferred to the platform with `call`; `resume` builds the
  state after the platform's answer. -/
  | external (call : NativeCall) (resume : NativeReturn → State)
  /-- The machine stopped by itself (a bare-metal `hlt`, a Wasm `end` of the
  start function). Hosted exits go through a terminal service request. -/
  | halted
  /-- Undefined, undecodable, or unauthorized: the machine is stuck. -/
  | fault (reason : Fault)

/-- A machine-code target. -/
structure ISA where
  /-- Canonical assembled instructions, with every operand resolved. -/
  Instr : Type
  /-- Canonical encoding of one instruction. -/
  encode : Instr → List UInt8
  /-- Decode one instruction from the head of a byte list, returning it and
  the number of bytes consumed. -/
  decode : List UInt8 → Option (Instr × Nat)
  /-- Decoding the canonical encoding recovers the instruction exactly and
  consumes exactly its bytes, whatever follows. -/
  decode_encode : ∀ (instr : Instr) (rest : List UInt8),
    decode (encode instr ++ rest) = some (instr, (encode instr).length)
  /-- No instruction encodes to nothing. -/
  encode_pos : ∀ instr : Instr, 0 < (encode instr).length
  /-- The assembled program an artifact format serializes and a loader
  installs. -/
  Raw : Type
  /-- What the platform hands the machine at entry: initial registers, the
  stack, the argument block. Defined by the ISA so the platform can fill it
  without knowing the state representation. -/
  InitialContext : Type
  /-- The whole machine state, memory included. -/
  State : Type
  /-- The loaded initial state of a program. -/
  initial : Raw → InitialContext → State
  /-- The register/memory view of a native call site the platform decodes. -/
  NativeCall : Type
  /-- The machine-level effect of a platform answer. -/
  NativeReturn : Type
  /-- Why a step could fault. -/
  Fault : Type
  /-- One instruction. -/
  step : State → StepOutcome State NativeCall NativeReturn Fault

namespace ISA

variable (isa : ISA)

/-- Canonical encoding of a whole instruction list. -/
def encodeAll : List isa.Instr → List UInt8
  | [] => []
  | instr :: rest => isa.encode instr ++ encodeAll rest

/-- Decode a whole byte list as a sequence of instructions, with fuel bounding
the number of instructions so the function is structurally total. -/
def decodeAll : Nat → List UInt8 → Option (List isa.Instr)
  | 0, bytes => if bytes = [] then some [] else none
  | fuel + 1, bytes =>
      if bytes = [] then some [] else
      match isa.decode bytes with
      | none => none
      | some (instr, consumed) =>
          if consumed = 0 then none
          else
            match decodeAll fuel (bytes.drop consumed) with
            | none => none
            | some rest => some (instr :: rest)

@[simp] theorem encodeAll_nil : isa.encodeAll [] = [] := rfl

@[simp] theorem encodeAll_cons (instr : isa.Instr) (rest : List isa.Instr) :
    isa.encodeAll (instr :: rest) = isa.encode instr ++ isa.encodeAll rest := rfl

theorem encodeAll_append (left right : List isa.Instr) :
    isa.encodeAll (left ++ right) = isa.encodeAll left ++ isa.encodeAll right := by
  induction left with
  | nil => rfl
  | cons instr rest ih => simp [ih, List.append_assoc]

/-- Decoding a canonical encoding with enough fuel recovers the instruction
list exactly. This is the theorem every ISA inherits from `decode_encode`;
no ISA proves its own version. -/
theorem decodeAll_encodeAll (code : List isa.Instr) (fuel : Nat)
    (enough : code.length ≤ fuel) :
    isa.decodeAll fuel (isa.encodeAll code) = some code := by
  induction code generalizing fuel with
  | nil =>
      cases fuel <;> simp [decodeAll]
  | cons instr rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have step : isa.decode (isa.encode instr ++ isa.encodeAll rest) =
              some (instr, (isa.encode instr).length) := isa.decode_encode instr _
          have pos := isa.encode_pos instr
          have consumedNonzero : (isa.encode instr).length ≠ 0 := Nat.pos_iff_ne_zero.mp pos
          have dropped : (isa.encode instr ++ isa.encodeAll rest).drop (isa.encode instr).length =
              isa.encodeAll rest := List.drop_left
          have nonempty : isa.encode instr ++ isa.encodeAll rest ≠ [] := by
            intro empty
            have lengths : (isa.encode instr ++ isa.encodeAll rest).length = 0 := by
              rw [empty]
              rfl
            rw [List.length_append] at lengths
            omega
          have restEnough : rest.length ≤ fuel := by
            rw [List.length_cons] at enough
            omega
          rw [encodeAll_cons, decodeAll, if_neg nonempty, step]
          dsimp only
          rw [if_neg consumedNonzero, dropped, ih fuel restEnough]

end ISA

end Grass.Target
