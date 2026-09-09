import Grass.ISA.X86.ImmediateArithmetic

/-!
Operand-local x86-64 register semantics for the Hello arithmetic family.

Authority: Intel SDM Vol. 1 §3.4.1.1/§3.4.3.1 and Vol. 2 ADD, SUB, CMP,
TEST, XOR, MOV instruction entries; AMD APM Vol. 1 flags/register sections and
Vol. 3 corresponding instruction entries. The AMD source migration repairs the
active retrieval pin, but this module's declaration-to-ledger attachment and
the profile's remaining confirmation debt stay open. Executable tests do not
discharge those obligations. See docs/AMD_SOURCE_MIGRATION.md.

Only ordinary register-direct 32/64-bit forms are admitted here. These are
operand/flag transfers, not a complete machine step: instruction fetch,
mode/prefix admission, RIP, interruption, memory and fault effects are separate.
Undefined AF after TEST/XOR is unconstrained, never silently preserved or zeroed.
The local Kind is one extensible operation family, not a master ISA sum type.
-/
namespace Grass.ISA.X86.RegisterSemantics

open Grass.ISA.X86

structure Flags (α : Type) where
  cf : α
  pf : α
  af : α
  zf : α
  sf : α
  of : α
deriving DecidableEq, Repr

def Flags.map {α β : Type} (f : α → β) (flags : Flags α) : Flags β :=
  ⟨f flags.cf, f flags.pf, f flags.af, f flags.zf, f flags.sf, f flags.of⟩

/-- Status bits only; no claim about reserved, RF, IF, DF or privilege bits. -/
def Flags.bits (flags : Flags Bool) : BitVec 64 :=
  (if flags.cf then 1 else 0) ||| (if flags.pf then 4 else 0) |||
  (if flags.af then 16 else 0) ||| (if flags.zf then 64 else 0) |||
  (if flags.sf then 128 else 0) ||| (if flags.of then 2048 else 0)

def Flags.fromBits (bits : BitVec 64) : Flags Bool :=
  ⟨bits.getLsbD 0, bits.getLsbD 2, bits.getLsbD 4,
   bits.getLsbD 6, bits.getLsbD 7, bits.getLsbD 11⟩

/-- `none` is undefined, not preserved. Preserved flags are `some` input. -/
def Flags.Allows (expected : Flags (Option Bool)) (actual : Flags Bool) : Prop :=
  (expected.cf = none ∨ expected.cf = some actual.cf) ∧
  (expected.pf = none ∨ expected.pf = some actual.pf) ∧
  (expected.af = none ∨ expected.af = some actual.af) ∧
  (expected.zf = none ∨ expected.zf = some actual.zf) ∧
  (expected.sf = none ∨ expected.sf = some actual.sf) ∧
  (expected.of = none ∨ expected.of = some actual.of)

instance (expected : Flags (Option Bool)) (actual : Flags Bool) :
    Decidable (expected.Allows actual) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def Flags.definedMask (flags : Flags (Option Bool)) : BitVec 64 :=
  (flags.map Option.isSome).bits

/-- Serialization representative only. The mask must accompany this value. -/
def Flags.valueBits (flags : Flags (Option Bool)) : BitVec 64 :=
  (flags.map (·.getD false)).bits

theorem Flags.exact_allows (flags : Flags Bool) :
    (flags.map some).Allows flags := by simp [Flags.Allows, Flags.map]

/-- Undefined flags do not make the permitted-result relation empty. -/
theorem Flags.allows_representative (flags : Flags (Option Bool)) :
    flags.Allows (flags.map (·.getD false)) := by
  have one (value : Option Bool) : value = none ∨ value = some (value.getD false) := by
    cases value <;> simp
  exact ⟨one flags.cf, one flags.pf, one flags.af, one flags.zf, one flags.sf, one flags.of⟩

def Flags.equal? (flags : Flags (Option Bool)) : Option Bool := flags.zf

/-- Unsigned JA is decidable from defined CF and ZF; unrelated undefined AF is irrelevant. -/
def Flags.above? (flags : Flags (Option Bool)) : Option Bool :=
  match flags.cf, flags.zf with
  | some carry, some zero => some (!carry && !zero)
  | _, _ => none

inductive Kind where
  | mov | add | sub | cmp | test | xor
deriving DecidableEq, Repr

private def parity {n : Nat} (value : BitVec n) : Bool :=
  !((List.range 8).foldl (fun odd i => xor odd (value.getLsbD i)) false)

private def arithmeticFlags {n : Nat} (subtract : Bool)
    (a b result : BitVec n) : Flags (Option Bool) :=
  let aSign := a.getLsbD (n-1)
  let bSign := b.getLsbD (n-1)
  let resultSign := result.getLsbD (n-1)
  { cf := some (if subtract then a.toNat < b.toNat else 2^n ≤ a.toNat+b.toNat)
    pf := some (parity result)
    af := some (if subtract then a.toNat%16 < b.toNat%16 else 16 ≤ a.toNat%16+b.toNat%16)
    zf := some (result == 0)
    sf := some resultSign
    of := some (if subtract then (aSign != bSign) && (resultSign != aSign)
                else (aSign == bSign) && (resultSign != aSign)) }

private def logicalFlags {n : Nat} (result : BitVec n) : Flags (Option Bool) :=
  ⟨some false, some (parity result), none, some (result == 0),
   some (result.getLsbD (n-1)), some false⟩

private structure NarrowEffect (n : Nat) where
  write : Option (BitVec n)
  flags : Flags (Option Bool)

private def narrow {n : Nat} (kind : Kind) (a b : BitVec n)
    (flags : Flags Bool) : NarrowEffect n :=
  match kind with
  | .mov => ⟨some b, flags.map some⟩
  | .add => let r := a+b; ⟨some r, arithmeticFlags false a b r⟩
  | .sub => let r := a-b; ⟨some r, arithmeticFlags true a b r⟩
  | .cmp => ⟨none, arithmeticFlags true a b (a-b)⟩
  | .test => ⟨none, logicalFlags (a &&& b)⟩
  | .xor => let r := a ^^^ b; ⟨some r, logicalFlags r⟩

structure Effect where
  /-- `none` means no destination write, including no w32 zero extension. -/
  write : Option (BitVec 64)
  flags : Flags (Option Bool)
deriving DecidableEq, Repr

/-- Width-sensitive transfer reuses the public partial-register write rule. -/
def evaluate (kind : Kind) (width : BasicInstructions.Width) (destination source : BitVec 64)
    (flags : Flags Bool) : Effect :=
  match width with
  | .w32 =>
    let effect := narrow kind (destination.setWidth 32) (source.setWidth 32) flags
    ⟨effect.write.map (writeBack .w32 destination), effect.flags⟩
  | .w64 =>
    let effect := narrow kind destination source flags
    ⟨effect.write.map (writeBack .w64 destination), effect.flags⟩

/-- Sign extension is selected by the same typed immediate as the encoder. -/
def evaluateImmediate (kind : ImmediateArithmetic.Kind) (width : BasicInstructions.Width)
    (destination : BitVec 64) (immediate : ImmediateArithmetic.Immediate)
    (flags : Flags Bool) : Effect :=
  evaluate (match kind with | .sub => .sub | .cmp => .cmp) width destination
    (BitVec.ofInt 64 immediate.toInt) flags

def Effect.destination (effect : Effect) (old : BitVec 64) : BitVec 64 :=
  effect.write.getD old

def Effect.Allows (effect : Effect) (old after : BitVec 64) (flags : Flags Bool) : Prop :=
  after = effect.destination old ∧ effect.flags.Allows flags

theorem cmp_no_write (width : BasicInstructions.Width) (a b : BitVec 64) (flags : Flags Bool) :
    (evaluate .cmp width a b flags).write = none := by cases width <;> rfl

theorem test_no_write (width : BasicInstructions.Width) (a b : BitVec 64) (flags : Flags Bool) :
    (evaluate .test width a b flags).write = none := by cases width <;> rfl

theorem cmp_sub_flags (width : BasicInstructions.Width) (a b : BitVec 64) (flags : Flags Bool) :
    (evaluate .cmp width a b flags).flags = (evaluate .sub width a b flags).flags := by
  cases width <;> rfl

theorem mov_preserves_flags (width : BasicInstructions.Width) (a b : BitVec 64) (flags : Flags Bool) :
    (evaluate .mov width a b flags).flags = flags.map some := by cases width <;> rfl

theorem logical_af_undefined (kind : Kind) (hk : kind = .test ∨ kind = .xor)
    (width : BasicInstructions.Width) (a b : BitVec 64) (flags : Flags Bool) :
    (evaluate kind width a b flags).flags.af = none := by
  rcases hk with rfl | rfl <;> cases width <;> rfl

theorem w32_write_clears_high (kind : Kind) (a b result : BitVec 64) (flags : Flags Bool)
    (h : (evaluate kind .w32 a b flags).write = some result) :
    BitVec.extractLsb' 32 32 result = 0 := by
  cases hw : (narrow kind (a.setWidth 32) (b.setWidth 32) flags).write with
  | none => simp [evaluate, hw, Option.map] at h
  | some value =>
    have hr : writeBack .w32 a value = result := by simpa [evaluate, hw, Option.map] using h
    rw [← hr]
    exact writeBack.w32_clears_high a value

/-- One register-only semantic family sharing the production encoding choices. -/
structure Instruction where
  kind : Kind
  width : BasicInstructions.Width
  destination : Gpr
  source : Gpr
deriving DecidableEq, Repr

def Instruction.encoding (instruction : Instruction) : InsnEncoding :=
  let w := instruction.width
  let d := instruction.destination
  let s := instruction.source
  match instruction.kind with
  | .mov => BasicInstructions.movRegReg w d s
  | .add => BasicInstructions.addRegReg w d s
  | .sub => BasicInstructions.subRegReg w d s
  | .cmp => BasicInstructions.cmpRegReg w d s
  | .test => BasicInstructions.testRegReg w d s
  | .xor => BasicInstructions.xorRegReg w d s

def Instruction.effect (instruction : Instruction) (registers : Gpr → BitVec 64)
    (flags : Flags Bool) : Effect :=
  evaluate instruction.kind instruction.width (registers instruction.destination)
    (registers instruction.source) flags

/-- Update the GPR file. `Instruction.comparison_preserves_registers` proves
CMP/TEST leave every register unchanged, including the destination's high half. -/
def Instruction.registersAfter (instruction : Instruction) (registers : Gpr → BitVec 64)
    (flags : Flags Bool) : Gpr → BitVec 64 :=
  fun reg => if reg = instruction.destination then
    (instruction.effect registers flags).destination (registers reg) else registers reg

theorem Instruction.preserves_other (instruction : Instruction) (registers : Gpr → BitVec 64)
    (flags : Flags Bool) (reg : Gpr) (h : reg ≠ instruction.destination) :
    instruction.registersAfter registers flags reg = registers reg := by
  simp [Instruction.registersAfter, h]

/-- Only the named operands and incoming status flags can affect this transfer. -/
theorem Instruction.effect_congr (instruction : Instruction) (before other : Gpr → BitVec 64)
    (flags : Flags Bool) (hd : before instruction.destination = other instruction.destination)
    (hs : before instruction.source = other instruction.source) :
    instruction.effect before flags = instruction.effect other flags := by
  simp only [Instruction.effect, hd, hs]

/-- Non-writing comparisons preserve the entire register file. -/
theorem Instruction.comparison_preserves_registers (instruction : Instruction)
    (hk : instruction.kind = .cmp ∨ instruction.kind = .test)
    (registers : Gpr → BitVec 64) (flags : Flags Bool) :
    instruction.registersAfter registers flags = registers := by
  funext reg
  have hw : (instruction.effect registers flags).write = none := by
    rcases hk with hk | hk
    · simp only [Instruction.effect, hk, cmp_no_write]
    · simp only [Instruction.effect, hk, test_no_write]
  simp [Instruction.registersAfter, Effect.destination, hw]

theorem Instruction.encoding_decodes (instruction : Instruction) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (instruction.encoding.toBytes ++ rest) = .ok (instruction.encoding, rest) := by
  cases instruction with
  | mk kind width destination source =>
    cases kind
    · exact BasicInstructions.movRegReg_decodes width destination source rest
    · exact BasicInstructions.addRegReg_decodes width destination source rest
    · exact BasicInstructions.subRegReg_decodes width destination source rest
    · exact BasicInstructions.cmpRegReg_decodes width destination source rest
    · exact BasicInstructions.testRegReg_decodes width destination source rest
    · exact BasicInstructions.xorRegReg_decodes width destination source rest

end Grass.ISA.X86.RegisterSemantics
