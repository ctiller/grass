import Grass.Assembly.SourceFrame

/-! Bounded lowering for source `arg Api.field, immediate` stack arguments.
The signature supplies the parameter index and admits only pointer parameters;
the Win64 convention then supplies the eight-byte stack slot and its offset.
The accepted nonnegative immediate subset is below `2^31`, exactly where the
`MOV r/m64, imm32` sign extension recovers the authored natural value. These
are allocation-relative geometry and decoder laws: no instruction execution,
physical RSP relation, call association, or memory effect is claimed here. -/
namespace Grass.Assembly.FrameArgument

open Grass.ABI.Win64 Grass.ISA.X86 Grass.Memory
open Grass.Platform.Win32.Signatures X86ControlFlow

structure Result where
  private mk ::
  frame : SourceFrame.Result
  item : CodeItem
  api : Api
  field : String
  value : Nat
  index : Nat
  parameter : Parameter
  rootOffset : Nat
  encoding : InsnEncoding
  member : item ∈ frame.program.collected.code
  instructionExact : item.instruction =
    ⟨.arg, [.qualified (apiName api) field, .immediate value]⟩
  apiExact : resolveName? (apiName api) = some api
  indexExact : argumentIndex? api field = some index
  parameterExact : (parameters api)[index]? = some parameter
  pointerKind : parameter.kind = .pointer
  arityFits : argumentCount api ≤ frame.layout.argumentCount
  stackPassed : registerArgumentCount ≤ index
  valueFitsSigned : value < 2 ^ 31
  displacementFitsSigned : shadowSpaceBytes + (index - registerArgumentCount) * 8 < 2 ^ 31
  encodingExact : movMem64Imm32 (.base .rsp
      (BitVec.ofNat 32 (shadowSpaceBytes + (index - registerArgumentCount) * 8)))
    (BitVec.ofNat 32 value) = some encoding

def Result.displacement (result : Result) : Nat :=
  shadowSpaceBytes + (result.index - registerArgumentCount) * 8

def Result.range (result : Result) : ByteRange :=
  ⟨result.rootOffset + result.displacement, 8⟩

def resolve? (frame : SourceFrame.Result) (rootOffset : Nat) (item : CodeItem) : Option Result :=
  if member : item ∈ frame.program.collected.code then
    match instruction : item.instruction with
    | ⟨.arg, [.qualified owner field, .immediate value]⟩ =>
      match apiEq : resolveName? owner with
      | none => none
      | some api =>
        match indexEq : argumentIndex? api field with
        | none => none
        | some index =>
          match parameterEq : (parameters api)[index]? with
          | none => none
          | some parameter =>
            if pointer : parameter.kind = .pointer then
              if arity : argumentCount api ≤ frame.layout.argumentCount then
                if stack : registerArgumentCount ≤ index then
                  if immediate : value < 2 ^ 31 then
                    let displacement := shadowSpaceBytes + (index - registerArgumentCount) * 8
                    if signed : displacement < 2 ^ 31 then
                      match encodingEq : movMem64Imm32
                          (.base .rsp (BitVec.ofNat 32 displacement))
                          (BitVec.ofNat 32 value) with
                      | none => none
                      | some encoding =>
                        some {
                          frame, item, api, field, value, index, parameter, rootOffset, encoding,
                          member, instructionExact := by
                            rw [resolveName?_exact apiEq]
                            exact instruction
                          apiExact := by rw [resolveName?_exact apiEq]; exact apiEq
                          indexExact := indexEq, parameterExact := parameterEq,
                          pointerKind := pointer, arityFits := arity, stackPassed := stack,
                          valueFitsSigned := immediate,
                          displacementFitsSigned := signed,
                          encodingExact := encodingEq }
                    else none
                  else none
                else none
              else none
            else none
    | _ => none
  else none

theorem Result.index_bounded (result : Result) : result.index < argumentCount result.api :=
  argumentIndex?_bounded result.indexExact

theorem resolve?_source {frame : SourceFrame.Result} {rootOffset : Nat} {item : CodeItem}
    {result : Result} (success : resolve? frame rootOffset item = some result) :
    result.frame = frame ∧ result.item = item ∧ result.rootOffset = rootOffset := by
  unfold resolve? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  dsimp only at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  exact ⟨rfl, rfl, rfl⟩

theorem Result.signed_immediate (result : Result) :
    (BitVec.ofNat 32 result.value).toInt = (result.value : Int) := by
  have valueFits := result.valueFitsSigned
  rw [show BitVec.ofNat 32 result.value = BitVec.ofInt 32 (result.value : Int) by rfl]
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · change (-2147483648 : Int) ≤ _
    omega
  · change (result.value : Int) < 2147483648
    change result.value < 2147483648 at valueFits
    omega

theorem Result.signed_displacement (result : Result) :
    (BitVec.ofNat 32 result.displacement).toInt = (result.displacement : Int) := by
  have displacementFits := result.displacementFitsSigned
  rw [show BitVec.ofNat 32 result.displacement =
    BitVec.ofInt 32 (result.displacement : Int) by rfl]
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · change (-2147483648 : Int) ≤ _
    omega
  · change (result.displacement : Int) < 2147483648
    change result.displacement < 2147483648 at displacementFits
    omega

theorem Result.stack_contains (result : Result) :
    (result.frame.layout.stackArgumentsRange.shift result.rootOffset).Contains result.range := by
  simp only [Result.range, Result.displacement, ByteRange.contains_def, ByteRange.shift,
    CallFrameLayout.stackArgumentsRange]
  have indexBound := result.index_bounded
  have arity := result.arityFits
  have stack := result.stackPassed
  change 4 ≤ result.index at stack
  simp only [CallFrameLayout.stackArgumentBytes, shadowSpaceBytes, registerArgumentCount]
  omega

theorem Result.frame_contains (result : Result) :
    (result.frame.layout.frameRange.shift result.rootOffset).Contains result.range :=
  ((ByteRange.shift_contains_iff _ _ result.rootOffset).mpr
    result.frame.layout.frame_contains_stackArguments).trans result.stack_contains

theorem Result.disjoint_local (result : Result) :
    result.range.Disjoint (result.frame.layout.localRange.shift result.rootOffset) := by
  have stackLocal := (ByteRange.shift_disjoint_iff _ _ result.rootOffset).mpr
    result.frame.layout.stackArguments_disjoint_local
  exact (stackLocal.symm.of_contains result.stack_contains).symm

theorem Result.encoding_decodes (result : Result) (rest : Grass.Std.Logical.ByteSeq) :
    decodeInsn (result.encoding.toBytes ++ rest) = .ok (result.encoding, rest) :=
  movMem64Imm32_decodes result.encodingExact rest

end Grass.Assembly.FrameArgument
