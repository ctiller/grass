import Grass.Std.Logical.Byte
import Grass.ISA.AArch64.Sources

/-!
A64 CBZ and SVC instruction-body boundary. This is a CPU projection, not a
machine-memory model. Fetch, exception routing, asynchronous exceptions, debug
events and provider execution are not defined here. `BodyStep` therefore must
not be substituted for a full machine transition in a program certificate.

Authority: Arm DDI 0602 ID032025, CBZ p.139 and SVC p.1009; see Sources.lean.
CBZ computes its normal control successor; SVC exposes the immediate to the
exception machinery, without asserting CheckForSVCTrap succeeds or EL1 entry.
-/
namespace Grass.ISA.AArch64

/-- Registers X0..X30. Encoding 31 is handled by the operand form, not stored. -/
abbrev Gpr := Fin 31

/-- CPU projection shared by the instruction bodies and platform adapters.
There is deliberately no memory field, stack geometry or exception-level state. -/
structure Cpu where
  gpr : Gpr → BitVec 64
  pc : BitVec 64
  nzcv : BitVec 4

/-- CBZ's Rt=31 is ZR, never SP. This function is not a universal register decoder. -/
def Cpu.readZero (cpu : Cpu) (rt : BitVec 5) : BitVec 64 :=
  if h : rt.toNat < 31 then cpu.gpr ⟨rt.toNat, h⟩ else 0

@[simp] theorem Cpu.readZero_zr (cpu : Cpu) : cpu.readZero 31 = 0 := by
  simp [Cpu.readZero]

/-- The encoded sf bit retains the exact 32/64-bit choice. -/
structure CompareZero where
  sf : BitVec 1
  imm19 : BitVec 19
  rt : BitVec 5
deriving DecidableEq, Repr

namespace CompareZero

def encode (instruction : CompareZero) : BitVec 32 :=
  instruction.sf ++ (0b0110100#7 ++ (instruction.imm19 ++ instruction.rt))

def offset (instruction : CompareZero) : BitVec 64 :=
  (instruction.imm19 ++ 0#2).signExtend 64

def isZero (instruction : CompareZero) (cpu : Cpu) : Bool :=
  if instruction.sf = 0 then (cpu.readZero instruction.rt).setWidth 32 == 0
  else cpu.readZero instruction.rt == 0

/-- The offset is relative to the instruction PC, not the fallthrough PC. -/
def nextPc (instruction : CompareZero) (cpu : Cpu) : BitVec 64 :=
  if instruction.isZero cpu then cpu.pc + instruction.offset else cpu.pc + 4

def execute (instruction : CompareZero) (cpu : Cpu) : Cpu :=
  { cpu with pc := instruction.nextPc cpu }

@[simp] theorem execute_gpr (instruction : CompareZero) (cpu : Cpu) :
    (instruction.execute cpu).gpr = cpu.gpr := rfl

@[simp] theorem execute_nzcv (instruction : CompareZero) (cpu : Cpu) :
    (instruction.execute cpu).nzcv = cpu.nzcv := rfl

theorem nextPc_cases (instruction : CompareZero) (cpu : Cpu) :
    (instruction.isZero cpu = true ∧
      (instruction.execute cpu).pc = cpu.pc + instruction.offset) ∨
    (instruction.isZero cpu = false ∧ (instruction.execute cpu).pc = cpu.pc + 4) := by
  cases h : instruction.isZero cpu <;> simp [execute, nextPc, h]

/-- Decode fields then check their exact encoding. CBNZ and other families fail. -/
def decode (word : BitVec 32) : Option CompareZero :=
  let instruction : CompareZero :=
    ⟨word.extractLsb' 31 1, word.extractLsb' 5 19, word.extractLsb' 0 5⟩
  if instruction.encode = word then some instruction else none

theorem decode_sound {word : BitVec 32} {instruction : CompareZero}
    (h : decode word = some instruction) : instruction.encode = word := by
  simp only [decode] at h
  split at h
  next heq => cases h; exact heq
  next => contradiction

@[simp] theorem decode_encode (instruction : CompareZero) :
    decode instruction.encode = some instruction := by
  have hs : instruction.encode.extractLsb' 31 1 = instruction.sf :=
    BitVec.extractLsb'_append_eq_left
  have hi : instruction.encode.extractLsb' 5 19 = instruction.imm19 := by
    rw [encode, BitVec.extractLsb'_append_eq_of_add_le (xhi := instruction.sf) (by decide),
      BitVec.extractLsb'_append_eq_of_add_le (xhi := 0b0110100#7) (by decide),
      BitVec.extractLsb'_append_eq_left]
  have hr : instruction.encode.extractLsb' 0 5 = instruction.rt := by
    rw [encode, BitVec.extractLsb'_append_eq_of_add_le (xhi := instruction.sf) (by decide),
      BitVec.extractLsb'_append_eq_of_add_le (xhi := 0b0110100#7) (by decide),
      BitVec.extractLsb'_append_eq_right]
  simp [decode, hs, hi, hr]

end CompareZero

namespace SupervisorCall

def encode (imm16 : BitVec 16) : BitVec 32 := 0b11010100000#11 ++ (imm16 ++ 1#5)

def decode (word : BitVec 32) : Option (BitVec 16) :=
  let immediate := word.extractLsb' 5 16
  if encode immediate = word then some immediate else none

theorem decode_sound {word : BitVec 32} {immediate : BitVec 16}
    (h : decode word = some immediate) : encode immediate = word := by
  simp only [decode] at h
  split at h
  next heq => cases h; exact heq
  next => contradiction

@[simp] theorem decode_encode (immediate : BitVec 16) :
    decode (encode immediate) = some immediate := by
  have hi : (encode immediate).extractLsb' 5 16 = immediate := by
    rw [encode, BitVec.extractLsb'_append_eq_of_add_le (xhi := 0b11010100000#11) (by decide),
      BitVec.extractLsb'_append_eq_left]
  simp [decode, hi]

/-- Exact decoded source and reached CPU. This receipt is a request to exception
machinery, NOT evidence of trap admission, Linux dispatch or provider completion.
A machine adapter must first establish that this word was actually fetched at
this CPU's PC and perform the selected profile's SVC checks/exception entry. -/
structure Request (word : BitVec 32) (before : Cpu) where
  immediate : BitVec 16
  decoded : decode word = some immediate

def request? (word : BitVec 32) (before : Cpu) : Option (Request word before) :=
  match h : decode word with
  | none => none
  | some immediate => some ⟨immediate, h⟩

theorem Request.source_exact {word : BitVec 32} {before : Cpu}
    (request : Request word before) : encode request.immediate = word :=
  decode_sound request.decoded

/-- No copied ABI snapshot: projection reads the very CPU indexing the receipt. -/
def Request.register {word : BitVec 32} {before : Cpu}
    (_request : Request word before) (reg : Gpr) : BitVec 64 := before.gpr reg

@[simp] theorem Request.register_exact {word : BitVec 32} {before : Cpu}
    (request : Request word before) (reg : Gpr) : request.register reg = before.gpr reg := rfl

end SupervisorCall

/-- Outcomes of this bounded body projection. No default fallthrough for SVC. -/
inductive BodyOutcome where
  | next (cpu : Cpu)
  | supervisor (immediate : BitVec 16)

/-- Fixed relation for the two supported bodies, independent of any caller goal.
This relation does not claim coverage of full machine transitions. -/
inductive BodyStep (word : BitVec 32) (before : Cpu) : BodyOutcome → Prop where
  | cbz (instruction : CompareZero) (decoded : CompareZero.decode word = some instruction) :
      BodyStep word before (.next (instruction.execute before))
  | svc (immediate : BitVec 16) (decoded : SupervisorCall.decode word = some immediate) :
      BodyStep word before (.supervisor immediate)

/-- Extract the existing SVC decode evidence, without running a second decoder.
This remains a body request, not exception-entry evidence. -/
def BodyStep.supervisorRequest {word : BitVec 32} {before : Cpu} {immediate : BitVec 16}
    (step : BodyStep word before (.supervisor immediate)) : SupervisorCall.Request word before := by
  refine ⟨immediate, ?_⟩
  cases step with
  | svc immediate decoded => exact decoded

/-- Every admitted body outcome retains its actual decode and condition or trap
request. No selected successful execution or arbitrary postcondition is used. -/
theorem bodyStep_cases {word : BitVec 32} {before : Cpu} {outcome : BodyOutcome}
    (step : BodyStep word before outcome) :
    (∃ instruction, CompareZero.decode word = some instruction ∧
      outcome = .next (instruction.execute before) ∧
      ((instruction.isZero before = true ∧
        (instruction.execute before).pc = before.pc + instruction.offset) ∨
       (instruction.isZero before = false ∧
        (instruction.execute before).pc = before.pc + 4))) ∨
    (∃ immediate, SupervisorCall.decode word = some immediate ∧
      outcome = .supervisor immediate) := by
  cases step with
  | cbz instruction decoded =>
      exact .inl ⟨instruction, decoded, rfl, instruction.nextPc_cases before⟩
  | svc immediate decoded => exact .inr ⟨immediate, decoded, rfl⟩

end Grass.ISA.AArch64
