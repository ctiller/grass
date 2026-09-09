import Tests.ISA.X86.CorpusCommon
import Grass.ISA.X86.RegisterSemantics

/-! Native validation data, never proof authority. Every expected register and
status-flag bit below is calculated by the public operand-local semantics; the
native runner remains an external observation, not a proof of those semantics.
RSP awaits the mapped-stack protocol and is deliberately excluded here. -/
namespace Grass.Tests.ISA.X86.NativeCorpus
open Grass.ISA.X86 Grass.ISA.X86.RegisterSemantics Grass.Tests.ISA.X86.Corpus

def registers : List Gpr := Gpr.all.filter (· != .rsp)

def initial : List (BitVec 64) := Gpr.all.map fun r =>
  BitVec.ofNat 64 (0xFEDCBA9876543210 + r.index.val * 0x102030405)

def initialFlags : Flags Bool := Flags.fromBits 0xAD7

def registerValue (state : List (BitVec 64)) (register : Gpr) : BitVec 64 :=
  state.getD register.index.val 0

def registersOf (state : List (BitVec 64)) : Gpr → BitVec 64 :=
  fun register => registerValue state register

def flagsText (flags : Flags (Option Bool)) : String :=
  hex64 flags.valueBits ++ "/" ++ hex64 flags.definedMask

def afterInstruction (before : List (BitVec 64)) (instruction : Instruction) : List (BitVec 64) :=
  Gpr.all.map fun register => instruction.registersAfter (registersOf before) initialFlags register

def afterImmediate (before : List (BitVec 64)) (destination : Gpr) (effect : Effect) : List (BitVec 64) :=
  Gpr.all.map fun register =>
    if register = destination then effect.destination (registerValue before register)
    else registerValue before register

def emit (label : String) (bytes : Grass.Std.Logical.ByteSeq)
    (before after : List (BitVec 64)) (flags : Flags (Option Bool))
    (basis : String) : IO Unit :=
  IO.println (String.intercalate "\t" [label, hexBytes bytes,
    String.intercalate "," (before.zipIdx.map fun (v, i) => if i == 4 then "-" else hex64 v),
    String.intercalate "," (after.zipIdx.map fun (v, i) => if i == 4 then "-" else hex64 v),
    "0xAD7", flagsText flags, basis])

def emitRegisterFrom (label : String) (instruction : Instruction) (before : List (BitVec 64))
    (basis : String) : IO Unit :=
  emit label instruction.encoding.toBytes before (afterInstruction before instruction)
    (instruction.effect (registersOf before) initialFlags).flags basis

def emitRegister (label : String) (instruction : Instruction) (basis : String) : IO Unit :=
  emitRegisterFrom label instruction initial basis

def widths : List BasicInstructions.Width := [.w32, .w64]

def widthText : BasicInstructions.Width → String
  | .w32 => "w32"
  | .w64 => "w64"

def kindText : Kind → String
  | .mov => "mov"
  | .add => "add"
  | .sub => "sub"
  | .cmp => "cmp"
  | .test => "test"
  | .xor => "xor"

def boundaryValues : BasicInstructions.Width → List (Nat × Nat)
  | .w32 => [(0, 0), (0, 1), (1, 1), (15, 1), (16, 1), (0xFFFFFFFF, 1),
             (0x7FFFFFFF, 1), (0x80000000, 1), (0x7FFFFFFF, 0x7FFFFFFF),
             (0x80000000, 0x80000000)]
  | .w64 => [(0, 0), (0, 1), (1, 1), (15, 1), (16, 1), (0xFFFFFFFFFFFFFFFF, 1),
             (0x7FFFFFFFFFFFFFFF, 1), (0x8000000000000000, 1),
             (0x7FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF),
             (0x8000000000000000, 0x8000000000000000)]

def boundaryState (width : BasicInstructions.Width) (destination source : Nat) : List (BitVec 64) :=
  let destination := match width with
    | .w32 => BitVec.ofNat 64 (0xA5A5A5A500000000 + destination)
    | .w64 => BitVec.ofNat 64 destination
  let source := match width with
    | .w32 => BitVec.ofNat 64 (0x5A5A5A5A00000000 + source)
    | .w64 => BitVec.ofNat 64 source
  (initial.set Gpr.rax.index.val destination).set Gpr.rcx.index.val source

def generate : IO Unit := do
  -- Existing complete non-RSP MOV matrix, now through production Instruction.
  for destination in registers do
    for source in registers do
      for width in widths do
        let instruction : Instruction := ⟨.mov, width, destination, source⟩
        emitRegister s!"mov-{destination.index.val}-{source.index.val}-{widthText width}"
          instruction "Instruction.encoding+Instruction.effect"
  -- Immediate rows share production immediate encoding and the matching semantics.
  for destination in registers do
    for width in widths do
      for immediate in ([.i8 0, .i8 127, .i8 128, .i8 255,
          .i32 0x7FFFFFFF, .i32 0x80000000, .i32 0xFFFFFFFF] :
          List ImmediateArithmetic.Immediate) do
        for kind in [ImmediateArithmetic.Kind.sub, .cmp] do
          let effect := evaluateImmediate kind width (registerValue initial destination) immediate initialFlags
          emit s!"arith-{destination.index.val}-{widthText width}-{repr kind}-{repr immediate}"
            (ImmediateArithmetic.encode kind width destination immediate).toBytes
            initial (afterImmediate initial destination effect) effect.flags
            "ImmediateArithmetic.encode+RegisterSemantics.evaluateImmediate"
  -- Six ordinary register families across width and arithmetic value boundaries.
  for kind in [Kind.mov, .add, .sub, .cmp, .test, .xor] do
    for width in widths do
      for ((destination, source), index) in (boundaryValues width).zipIdx do
        let instruction : Instruction := ⟨kind, width, .rax, .rcx⟩
        emitRegisterFrom s!"boundary-{kindText kind}-{widthText width}-{index}"
          instruction (boundaryState width destination source) "Instruction.encoding+Instruction.effect"
  -- Exact operations emitted by the current Hello lowering path.
  for (label, instruction) in
      [ ("hello-test-eax-eax", ⟨.test, .w32, .rax, .rax⟩)
      , ("hello-cmp-eax-r14d", ⟨.cmp, .w32, .rax, .r14⟩)
      , ("hello-add-r13-rax", ⟨.add, .w64, .r13, .rax⟩)
      , ("hello-sub-r14d-eax", ⟨.sub, .w32, .r14, .rax⟩) ] do
    emitRegister label instruction "Hello-production-Instruction.encoding+Instruction.effect"

end Grass.Tests.ISA.X86.NativeCorpus

def main : IO Unit := Grass.Tests.ISA.X86.NativeCorpus.generate
