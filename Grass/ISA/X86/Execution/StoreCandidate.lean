import Grass.ISA.X86.Execution.DecodedSite
import Grass.ISA.X86.Execution.State

/-!
# Bounded decoded store-candidate evidence

This module recognizes the first imported-C corpus forms, `MOV dword ptr
[base], imm32` and `MOV dword ptr [base+disp8], imm32`, directly from a
production `DecodedSite`. Its result is
available before memory resolution or `Op.step`, so a ghost-memory denial does
not erase the decoded candidate address and width which still require diagnosis.

This is deliberately narrower than an x86 execution relation.  In particular,
`check` assumes the supplied architectural state is the state at the decoded
instruction and records the instruction's candidate write footprint; it does
not prove reachability, successful completion, a committed write, or memory
safety. The external rules are Intel SDM revision 092 Vol. 2D `MOV`, pp.
4-28--4-30, together with the 64-bit ModR/M addressing tables, and AMD APM
publication 24594 revision 3.38 `MOV`, pp. 240--242, together with its
default-address-size ModR/M rules. These are the existing primary sources in
`docs/REFERENCES.md` and `Grass.ISA.X86.Profile`; `check`, `BaseDisplacement.value`,
`Evidence.address`, and `Evidence.width` retain explicit modeled-function ledger
debt until registered by the owning x86 audit.
-/
namespace Grass.ISA.X86.Execution.StoreCandidate

open Grass.Core Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution

private theorem decodedLowBase (rm : BitVec 3) : (Gpr.ofBits 0 rm).rexBit = false := by
  revert rm
  decide

private theorem decodedLowBase_bits (rm : BitVec 3) :
    (Gpr.ofBits 0 rm).encodingBits = rm := by
  revert rm
  decide

/-- The two base-register displacement forms in the bounded candidate profile. -/
inductive BaseDisplacement where
  | none
  | disp8 (bits : BitVec 8)
deriving DecidableEq, Repr

namespace BaseDisplacement

def encoded : BaseDisplacement → Displacement
  | .none => .none
  | .disp8 bits => .d8 bits

def modBits : BaseDisplacement → BitVec 2
  | .none => ModRm.modNoDisplacement
  | .disp8 _ => ModRm.modDisp8

def value : BaseDisplacement → BitVec 32
  | .none => 0
  | .disp8 bits => BitVec.signExtend 32 bits

end BaseDisplacement

private theorem decodeLowBaseDisp8 (rm : BitVec 3) (displacement : BitVec 8)
    (notSib : rm ≠ ModRm.rmSelectsSib) :
    decodeMem
      { mod := ModRm.modDisp8, rm := (Gpr.ofBits 0 rm).encodingBits, sib := none
        disp := .d8 displacement, rexX := 0, rexB := 0 } =
      some (.base (Gpr.ofBits 0 rm) (BitVec.signExtend 32 displacement)) := by
  revert notSib displacement rm
  decide

private theorem decodeLowBaseNone (rm : BitVec 3)
    (notSib : rm ≠ ModRm.rmSelectsSib)
    (notRip : rm ≠ ModRm.rmSelectsRipRelative) :
    decodeMem
      { mod := ModRm.modNoDisplacement, rm := (Gpr.ofBits 0 rm).encodingBits, sib := none
        disp := .none, rexX := 0, rexB := 0 } =
      some (.base (Gpr.ofBits 0 rm) 0) := by
  revert notRip notSib rm
  decide

/-- Refusal reasons for the intentionally small first imported-store profile. -/
inductive Error where
  | site (error : DecodedSite.Error)
  | unsupportedInstruction
  | stateRipMismatch
  | addressWrap
deriving DecidableEq, Repr

/-- Kernel-checkable evidence for a decoded candidate four-byte write. `addressFits`
keeps the byte footprint linear rather than silently wrapping at `2^64`.
The immediate is retained because it identifies the decoded store, but no
claim is made that these bytes were committed to memory. -/
structure Evidence (rip : BitVec 64) (bytes : ByteSeq) (state : State) where
  site : DecodedSite rip bytes
  base : Gpr
  displacement : BaseDisplacement
  immediate : BitVec 32
  rexNone : site.encoding.rex = none
  directOpcode : site.encoding.escape = false ∧ site.encoding.opcode = 0xC7
  modrmShape : site.encoding.modrm =
    some ⟨displacement.modBits, 0, base.encodingBits⟩
  noSib : site.encoding.sib = none
  displacementShape : site.encoding.disp = displacement.encoded
  immediateShape : site.encoding.imm = .i32 immediate
  baseLow : base.rexBit = false
  decodedMemory :
    decodeMem
      { mod := displacement.modBits, rm := base.encodingBits, sib := none
        disp := displacement.encoded, rexX := 0, rexB := 0 } =
      some (.base base displacement.value)
  atInstruction : state.rip = rip
  addressFits :
    (state.gpr base + BitVec.signExtend 64 displacement.value).toNat + 4 ≤
      2 ^ 64

namespace Evidence

def operand {rip bytes state} (e : Evidence rip bytes state) : MemOperand :=
  .base e.base e.displacement.value

theorem decodedMemory_operand {rip bytes state} (e : Evidence rip bytes state) :
    decodeMem
      { mod := e.displacement.modBits, rm := e.base.encodingBits, sib := none
        disp := e.displacement.encoded, rexX := 0, rexB := 0 } = some e.operand :=
  e.decodedMemory

/-- The production writer accepts the decoded semantic operand. Its canonical
encoding uses the writer's deliberate disp32 policy, so this is semantic
re-encoding evidence, not equality with the imported short disp8 bytes. -/
theorem productionEncoder_accepts {rip bytes state} (e : Evidence rip bytes state) :
    (movMem32Imm32 e.operand e.immediate).isSome := by
  simp only [operand, movMem32Imm32, encodeMemInsn, encodeMem]
  split <;> rfl

def productionEncoding {rip bytes state} (e : Evidence rip bytes state) : InsnEncoding :=
  (movMem32Imm32 e.operand e.immediate).getD default

theorem productionEncoding_eq {rip bytes state} (e : Evidence rip bytes state) :
    movMem32Imm32 e.operand e.immediate = some e.productionEncoding := by
  cases h : movMem32Imm32 e.operand e.immediate with
  | none =>
      have accepted := productionEncoder_accepts e
      simp [h] at accepted
  | some encoding => simp [productionEncoding, h]

theorem productionEncoding_decodes {rip bytes state} (e : Evidence rip bytes state)
    (rest : ByteSeq) :
    decodeInsn (e.productionEncoding.toBytes ++ rest) =
      .ok (e.productionEncoding, rest) :=
  movMem32Imm32_decodes e.productionEncoding_eq rest

/-- Candidate effective address for the decoded `[base+disp8]` operand.
No general x86 memory-address evaluator currently exists in `Grass.ISA.X86`;
this scoped mapping is therefore externally defined behavior that must remain
in the modeled-function audit alongside the `C7 /0` and width-four choices.
Bit-vector addition models architectural address addition;
`addressFits` separately establishes that this four-byte footprint does not
cross the end of the address space. It does not prove canonical addresses,
segment/mode applicability, access permissions, or instruction execution.
This candidate mapping must converge on the ISA owner's address/attempt
semantics once available; it is not a parallel execution authority. -/
def address {rip bytes state} (e : Evidence rip bytes state) : BitVec 64 :=
  state.gpr e.base + BitVec.signExtend 64 e.displacement.value

def width {rip bytes state} (_e : Evidence rip bytes state) : Nat := 4

@[simp] theorem width_eq {rip bytes state} (e : Evidence rip bytes state) : e.width = 4 := rfl

theorem footprint_noWrap {rip bytes state} (e : Evidence rip bytes state) :
    e.address.toNat + e.width ≤ 2 ^ 64 := e.addressFits

end Evidence

/-- Check exact bytes with the production decoder, recognize the bounded
`C7 /0` form, and calculate its candidate footprint from canonical `State.gpr`.
The caller supplies `state` under the callable-entry prerequisite that its RIP
is the store instruction. -/
def check (rip : BitVec 64) (bytes : ByteSeq) (state : State) :
    Except Error (Evidence rip bytes state) :=
  match hs : DecodedSite.check rip bytes with
  | .error error => .error (.site error)
  | .ok site =>
      match he : site.encoding with
      | { rex := none, escape := false, opcode := 0xC7,
          modrm := some modrm, sib := none, disp := .none,
          imm := .i32 immediate } =>
          if hm : modrm.mod = ModRm.modNoDisplacement ∧ modrm.reg = 0 ∧
              modrm.rm ≠ ModRm.rmSelectsSib ∧
              modrm.rm ≠ ModRm.rmSelectsRipRelative then
            let base := Gpr.ofBits 0 modrm.rm
            if hr : state.rip = rip then
              let address := state.gpr base
              if hf : address.toNat + 4 ≤ 2 ^ 64 then
                .ok {
                  site := site
                  base := base
                  displacement := .none
                  immediate := immediate
                  rexNone := by simp [he]
                  directOpcode := by simp [he]
                  modrmShape := by
                    rw [he]
                    obtain ⟨hmod, hreg, _, _⟩ := hm
                    apply congrArg some
                    cases modrm with
                    | mk md rg rm =>
                      simp only at hmod hreg ⊢
                      subst md
                      subst rg
                      congr
                      exact (decodedLowBase_bits rm).symm
                  noSib := by simp [he]
                  displacementShape := by simp [he, BaseDisplacement.encoded]
                  immediateShape := by simp [he]
                  baseLow := decodedLowBase modrm.rm
                  decodedMemory := decodeLowBaseNone modrm.rm hm.2.2.1 hm.2.2.2
                  atInstruction := hr
                  addressFits := by simpa [BaseDisplacement.value] using hf }
              else .error .addressWrap
            else .error .stateRipMismatch
          else .error .unsupportedInstruction
      | { rex := none, escape := false, opcode := 0xC7,
          modrm := some modrm, sib := none, disp := .d8 displacement,
          imm := .i32 immediate } =>
          if hm : modrm.mod = ModRm.modDisp8 ∧ modrm.reg = 0 ∧
              modrm.rm ≠ ModRm.rmSelectsSib then
            let base := Gpr.ofBits 0 modrm.rm
            if hr : state.rip = rip then
              let address := state.gpr base +
                BitVec.signExtend 64 (BitVec.signExtend 32 displacement)
              if hf : address.toNat + 4 ≤ 2 ^ 64 then
                .ok {
                  site := site
                  base := base
                  displacement := .disp8 displacement
                  immediate := immediate
                  rexNone := by simp [he]
                  directOpcode := by simp [he]
                  modrmShape := by
                    rw [he]
                    obtain ⟨hmod, hreg, _⟩ := hm
                    apply congrArg some
                    cases modrm with
                    | mk md rg rm =>
                      simp only at hmod hreg ⊢
                      subst md
                      subst rg
                      congr
                      exact (decodedLowBase_bits rm).symm
                  noSib := by simp [he]
                  displacementShape := by simp [he, BaseDisplacement.encoded]
                  immediateShape := by simp [he]
                  baseLow := decodedLowBase modrm.rm
                  decodedMemory := decodeLowBaseDisp8 modrm.rm displacement hm.2.2
                  atInstruction := hr
                  addressFits := hf }
              else .error .addressWrap
            else .error .stateRipMismatch
          else .error .unsupportedInstruction
      | _ => .error .unsupportedInstruction

end Grass.ISA.X86.Execution.StoreCandidate
