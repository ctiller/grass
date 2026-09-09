import Grass.Assembly.SignedRel32
import Grass.ISA.X86.Decode

/-! Checked RIP-relative operands for static addresses and import slots.
The target is a byte offset supplied by layout; this module does not establish
symbol binding, mapped memory, or indirect-call execution. Instruction size is
computed by the same encoder used for the final displacement. -/
namespace Grass.Assembly.RipRelative

open Grass.ISA.X86 Grass.Std.Logical

inductive Kind where
  | address (destination : Gpr)
  | indirectCall
deriving DecidableEq, Repr

def encode? (kind : Kind) (bits : BitVec 32) : Option InsnEncoding :=
  match kind with
  | .address destination => leaR64 destination (.ripRelative bits)
  | .indirectCall => callMem64 (.ripRelative bits)

theorem encode?_decodes {kind : Kind} {bits : BitVec 32} {encoding : InsnEncoding}
    (success : encode? kind bits = some encoding) (rest : ByteSeq) :
    decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest) := by
  cases kind with
  | address destination => exact leaR64_decodes success rest
  | indirectCall => exact callMem64_decodes success rest

structure Result where
  private mk ::
  kind : Kind
  sourceOffset : Nat
  targetOffset : Nat
  template : InsnEncoding
  displacement : SignedRel32.Resolved
  encoding : InsnEncoding
  templateExact : encode? kind 0 = some template
  displacementExact : SignedRel32.resolve? sourceOffset template.size targetOffset =
    some displacement
  encodingExact : encode? kind displacement.bits = some encoding
  sizeExact : encoding.size = template.size

def resolve? (kind : Kind) (sourceOffset targetOffset : Nat) : Option Result := do
  match templateExact : encode? kind 0 with
  | none => none
  | some template =>
    match displacementExact : SignedRel32.resolve? sourceOffset template.size targetOffset with
    | none => none
    | some displacement =>
      match encodingExact : encode? kind displacement.bits with
      | none => none
      | some encoding =>
        if sizeExact : encoding.size = template.size then
          some ⟨kind, sourceOffset, targetOffset, template, displacement, encoding,
            templateExact, displacementExact, encodingExact, sizeExact⟩
        else none

theorem resolve?_exact {kind : Kind} {sourceOffset targetOffset : Nat} {result : Result}
    (success : resolve? kind sourceOffset targetOffset = some result) :
    result.kind = kind ∧ result.sourceOffset = sourceOffset ∧ result.targetOffset = targetOffset := by
  unfold resolve? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  exact ⟨rfl, rfl, rfl⟩

theorem Result.target_equation (result : Result) :
    (result.targetOffset : Int) = (result.sourceOffset : Int) +
      (result.encoding.toBytes.length : Int) + result.displacement.bits.toInt := by
  have target := SignedRel32.target_equation_of_resolve? result.displacementExact
  simpa only [InsnEncoding.length_toBytes, result.sizeExact] using target

theorem Result.encoding_decodes (result : Result) (rest : ByteSeq) :
    decodeInsn (result.encoding.toBytes ++ rest) = .ok (result.encoding, rest) :=
  encode?_decodes result.encodingExact rest

end Grass.Assembly.RipRelative
