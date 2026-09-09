import Tests.ISA.X86.CorpusCommon
import Grass.ISA.X86.BasicInstructions
import Grass.ISA.X86.ImmediateArithmetic

/-! Native validation data, never proof authority. Register MOV predictions use
the public writeBack rule. Arithmetic rows test encoding and signed-immediate
interpretation with a test-local arithmetic expression; flags remain observed,
not asserted to be implemented instruction semantics. RSP awaits a mapped-stack
protocol and is deliberately excluded from this first campaign. -/
namespace Grass.Tests.ISA.X86.NativeCorpus
open Grass.ISA.X86 Grass.Tests.ISA.X86.Corpus

def registers : List Gpr := Gpr.all.filter (· != .rsp)

def initial : List (BitVec 64) := Gpr.all.map fun r =>
  BitVec.ofNat 64 (0xFEDCBA9876543210 + r.index.val * 0x102030405)

def emit (label : String) (bytes : Grass.Std.Logical.ByteSeq)
    (before after : List (BitVec 64)) (flags : Option (BitVec 64))
    (basis : String) : IO Unit :=
  IO.println (String.intercalate "\t" [label, hexBytes bytes,
    String.intercalate "," (before.zipIdx.map fun (v, i) => if i == 4 then "-" else hex64 v),
    String.intercalate "," (after.zipIdx.map fun (v, i) => if i == 4 then "-" else hex64 v),
    "0xAD7", flags.map hex64 |>.getD "-", basis])

def generate : IO Unit := do
  for dst in registers do
    for src in registers do
      for wide in [false, true] do
        let value := initial.getD src.index.val 0
        let result := if wide then writeBack .w64 (initial.getD dst.index.val 0) value
          else writeBack .w32 (initial.getD dst.index.val 0) (value.setWidth 32)
        emit s!"mov-{dst.index.val}-{src.index.val}-{wide}"
          (BasicInstructions.movRegReg (if wide then .w64 else .w32) dst src).toBytes
          initial (initial.set dst.index.val result) (some 0xAD7) "writeBack"
  for dst in registers do
    for wide in [false, true] do
      for immediate in ([.i8 0, .i8 127, .i8 128, .i8 255,
          .i32 0x7FFFFFFF, .i32 0x80000000, .i32 0xFFFFFFFF] :
          List ImmediateArithmetic.Immediate) do
        for kind in [ImmediateArithmetic.Kind.sub, .cmp] do
          let old := initial.getD dst.index.val 0
          let difference := old.toInt - immediate.toInt
          let result := if wide then writeBack .w64 old (BitVec.ofInt 64 difference)
            else writeBack .w32 old (BitVec.ofInt 32 difference)
          let after := if kind == .cmp then initial else initial.set dst.index.val result
          let encoding := ImmediateArithmetic.encode kind (if wide then .w64 else .w32)
            dst immediate
          emit s!"arith-{dst.index.val}-{wide}-{repr kind}-{repr immediate}"
            encoding.toBytes initial after none
            (if kind == .cmp then "cmp-completion+gpr-nonmutation"
             else "encoding+immediate.toInt+test-arithmetic")

end Grass.Tests.ISA.X86.NativeCorpus

def main : IO Unit := Grass.Tests.ISA.X86.NativeCorpus.generate
