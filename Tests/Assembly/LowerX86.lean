import Grass.Assembly.Lower.X86

/-! Generic memory lowering regressions. `#guard` checks compiled examples;
`Lowering.lower_size` remains the universal layout proof. -/
namespace Tests.Assembly.LowerX86
open Grass.Assembly.Syntax Grass.Assembly.Lower Grass.Assembly.Lower.X86
open Grass.ISA.X86 Grass.ISA.X86.Target

local instance : DecidableEq Grass.ISA.X86.isa.Instr :=
  inferInstanceAs (DecidableEq Instr)

def env : Env := Env.ofLocals 8
  [⟨"wide", "UInt64", 0⟩, ⟨"count", "UInt32", 0⟩]
  (fun name => if name = "offset" then some (-16) else none) (fun _ => none)

def bytes (op : String) (args : List Operand) (pc : Nat := 0x1000)
    (labels : String → Option Nat := fun _ => none) : Except String (List UInt8) :=
  (lower (.instruction op args []) env labels pc).map Grass.ISA.X86.isa.encodeAll

def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def succeedsWith {α : Type} [DecidableEq α] (result : Except String α) (expected : α) : Bool :=
  match result with
  | .ok actual => decide (actual = expected)
  | .error _ => false

def mem (width : Option MemSize) (base : String) (disp : Int) : Operand :=
  .mem width (some base) none (.int disp)

-- Fixed SIB/disp32 encoding, extended registers, negative and named offsets.
#guard succeedsWith (bytes "mov" [.reg "eax", .local "count"]) [0x8b, 0x84, 0x24, 8, 0, 0, 0]
#guard succeedsWith (bytes "mov" [.reg "r9", mem (some .qword) "r12" (-16)]) [0x4d, 0x8b, 0x8c, 0x24, 0xf0, 0xff, 0xff, 0xff]
#guard succeedsWith (bytes "lea" [.reg "r9", .localAddress "count"]) [0x4c, 0x8d, 0x8c, 0x24, 8, 0, 0, 0]
#guard succeedsWith (bytes "lea" [.reg "rax", .mem none (some "rbx") none (.symbol "offset")]) [0x48, 0x8d, 0x84, 0x23, 0xf0, 0xff, 0xff, 0xff]
#guard succeedsWith (bytes "mov" [.local "count", .imm 0]) [0xc7, 0x84, 0x24, 8, 0, 0, 0, 0, 0, 0, 0]
#guard succeedsWith (bytes "mov" [.local "wide", .imm (-1)]) [0x48, 0xc7, 0x84, 0x24, 0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff]
#guard succeedsWith (bytes "lea" [.reg "rax", .mem none none none (.ripRelative "back")]
  0x1000 (fun _ => some 0xff0)) [0x48, 0x8d, 5, 0xe9, 0xff, 0xff, 0xff]
#guard succeedsWith (bytes "call" [.mem (some .qword) none none (.ripRelative "slot")]
  0x1000 (fun _ => some 0x1010)) [0xff, 0x15, 10, 0, 0, 0]

-- Width, displacement, addressing-mode, and unresolved-name refusals.
#guard failed (bytes "mov" [.reg "rax", .local "count"])
#guard failed (bytes "mov" [.reg "eax", .local "absent"])
#guard failed (bytes "mov" [.reg "eax", .localAddress "count"])
#guard failed (bytes "mov" [.reg "eax", mem (some .qword) "rax" 0])
#guard failed (bytes "mov" [mem none "rax" 0, .imm 1])
#guard failed (bytes "mov" [mem (some .byte) "rax" 0, .imm 1])
#guard failed (bytes "mov" [.local "wide", .imm 2147483648])
#guard failed (bytes "mov" [.reg "eax", mem none "rax" 2147483648])
#guard failed (bytes "mov" [.reg "eax", mem none "rax" (-2147483649)])
#guard failed (bytes "mov" [.reg "eax", .mem none (some "rax") none (.symbol "absent")])
#guard failed (bytes "mov" [.reg "eax", .mem none (some "rax") (some ("rcx", 2)) (.int 0)])
#guard failed (bytes "mov" [.reg "eax", .mem none (some "rax") none (.int 0) .postIndex])
#guard failed (bytes "lea" [.reg "eax", mem none "rax" 0])
#guard failed (bytes "call" [.mem (some .dword) none none (.ripRelative "slot")])
#guard failed (bytes "call" [.mem none none none (.ripRelative "absent")])
#guard failed (finish (.callRip "far") (fun _ => some (6 + 2147483648)) 0)
#guard failed (finish (.leaRip .rax "far") (fun _ => some 0) 2147483642)
#guard !(failed (finish (.callRip "edge") (fun _ => some (6 + 2147483647)) 0))
#guard !(failed (finish (.leaRip .rax "edge") (fun _ => some 0) 2147483641))
#guard !(failed (bytes "mov" [.reg "eax", mem none "rax" (-2147483648)]))
#guard !(failed (bytes "mov" [.reg "eax", mem none "rax" 2147483647]))

-- Local allocation metadata keeps first-binding semantics and allocation bounds.
#guard localSizeLookup 8 [⟨"x", "Unknown", 0⟩, ⟨"x", "UInt32", 0⟩] "x" = none
#guard localSizeLookup 4 [⟨"x", "UInt64", 0⟩, ⟨"x", "UInt32", 0⟩] "x" = none
#guard failed (memoryWidth { env with frameBytes := 11 } (.local "count"))
#guard failed (memoryWidth { env with localSize := fun _ => none } (.local "count"))

-- Seven memory operations assembled with one shared code/data/import layout.
-- No platform names or program-specific lowering paths participate.
def source : Source where
  locals := []
  callFrame := []
  lines := [
    .label "entry" [],
    .instruction "mov" [.local "count", .imm 0] [],
    .instruction "mov" [.reg "eax", .local "count"] [],
    .instruction "lea" [.reg "r9", .localAddress "count"] [],
    .instruction "lea" [.reg "r13", .mem none none none (.ripRelative "data")] [],
    .instruction "call" [.mem (some .qword) none none (.ripRelative "__imp_service")] [],
    .instruction "call" [.mem (some .qword) none none (.ripRelative "__imp_service")] [],
    .instruction "call" [.mem (some .qword) none none (.ripRelative "__imp_service")] [],
    .instruction "ret" [] []]

def placement (base : Nat) : Placement where
  codeBase := base
  rodata := [("data", [1, 2, 3])]
  dataBase := none
  imports := [("library", "service")]
  importBase := none
  entry := "entry"
  stackBytes := 16

def sameInstructions (a b : List Instr) : Bool := decide (a = b)

def layoutChecks (base : Nat) : Bool :=
  match assemble lowering source env (placement base) with
  | .error _ => false
  | .ok (instrs, artifact) =>
      sameInstructions instrs [Instr.movMI32 .w32 .rsp 8 0, .movRM .w32 .rax .rsp 8,
        .leaRM .r9 .rsp 8, .leaRip .r13 19, .callRip 16, .callRip 10,
        .callRip 4, .ret] &&
      (Grass.ISA.X86.isa.encodeAll instrs).length == 52 &&
      artifact.entry == base &&
      artifact.sections.map (·.virtualAddress) == [base, base + 52, base + 55]

#guard layoutChecks 0x1000
#guard layoutChecks 0x400000
#guard succeedsWith (lowering.sizes env source.lines) 52
-- A branch spans two memory instructions; pass 1 must count their real widths.
def branchSource : Source where
  locals := []
  callFrame := []
  lines := [.label "entry" [], .instruction "jmp" [.symbol "done"] [],
    .instruction "lea" [.reg "rax", mem none "rbx" 0] [],
    .instruction "mov" [.local "count", .imm 4294967295] [],
    .label "done" [], .instruction "ret" [] []]

#guard succeedsWith ((assemble lowering branchSource env (placement 0x1000)).map (fun result =>
  result.1)) [Instr.jmpRel32 19, .leaRM .rax .rbx 0,
    .movMI32 .w32 .rsp 8 4294967295, .ret]
#guard !(failed (bytes "mov" [.local "wide", .imm 2147483647]))
end Tests.Assembly.LowerX86
