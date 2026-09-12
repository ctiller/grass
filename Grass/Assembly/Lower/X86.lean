import Grass.Assembly.Lower.Layout
import Grass.Assembly.Lower.X86Lengths
import Grass.Assembly.Syntax.Parser
import Grass.ISA.X86.Target

/-!
# The x86-64 instance of the lowering seam

`Grass.Assembly.Lower.X86.lowering` fills `Lowering Grass.ISA.X86.isa` for
exactly the instruction families `Grass/ISA/X86/Target/Encode.lean`'s
`Instr` encodes today, mirroring the structure and proof pattern of
`Grass/Assembly/Lower/AArch64.lean`. Unlike A64 (one instruction, one word),
x86-64 instruction lengths vary with the operand widths and with which
registers need a REX prefix, so `size` and `lower` share one classification
step (`resolve`/`Resolved`) rather than `size` being a constant: the two
passes must agree on *which* `Instr` a line becomes, and `Resolved.length`
is exactly the byte count that choice commits to.

## Mnemonic table

| written | operands | encoded family |
| --- | --- | --- |
| `mov` | `r64/r32, r64/r32` (same width) | `movRR` |
| `mov` | `r32, imm` | `movRI32` |
| `mov` | `r64, imm` | `movRI32` (zero-extends) when `0 ≤ imm < 2^32`, else `movRI64` |
| `movzx`, `movsx` | `r32/r64, r8` or `r32/r64, r16` | `movzxRR`/`movsxRR` |
| `add`, `sub`, `and`, `or`, `xor`, `cmp` | `r, r` (same width) | `aluRR` |
| `add`, `sub`, `and`, `or`, `xor`, `cmp` | `r, imm` | `aluRI` |
| `test` | `r, r` (same width) | `testRR` |
| `test` | `r, imm` | `testRI` |
| `shl`, `shr`, `sar` | `r, imm8` | `shiftImm` |
| `imul` | `r, r` (same width) | `imul2` |
| `inc`, `dec` | `r` | `inc`/`dec` |
| `push`, `pop` | `r64` | `push`/`pop` |
| `div`, `idiv`, `mul` | `r` | `div`/`idiv`/`mul` |
| `setcc` (`sete`, `setne`, ...) | `r8` | `setcc` |
| `cmovcc` (`cmove`, `cmovne`, ...) | `r, r` (same width) | `cmovcc` |
| `xchg` | `r, r` (same width) | `xchgRR` |
| `jmp` | `label` | `jmpRel32` (canonical: never `jmpRel8`) |
| `jz`/`je`/`jne`/`ja`/`jb`/`jae`/`jbe`/`jl`/`jle`/`jg`/`jge`/`js`/`jns`/... | `label` | `jccRel32` (canonical: never `jccRel8`) |
| `call`, `call_local` | `label` | `callRel32` |
| `ret`, `ud2`, `hlt`, `nop`, `syscall`, `cdq`, `cqo` | (none) | themselves |

`call_local` is accepted as a synonym for direct `call`. Every mnemonic/operand
shape outside this table and the memory forms below, and every register
spelling narrower than 32 bits outside the specific slots above (`setcc`'s
and `movzx`/`movsx`'s 8/16-bit source), is refused with a message naming the
line: this profile's `Instr` has no `Sz` narrower than 32 bits, so a general
register operand is only ever 32- or 64-bit.

## Memory operands

`movRM`, `movMI32`, `leaRM`, `leaRip`, and `callRip` lower through the
canonical ISA constructors. Base forms use a mandatory SIB and signed
disp32; their size comes directly from `encode`. RIP forms resolve symbols
relative to the instruction end, with lengths proved in `X86Lengths`.
`lea` accepts 64-bit destinations. Memory MOV checks explicit or declared
local widths; an immediate store requires a known dword or qword width.
Unknown constants, locals, widths, unsupported addressing modes, and
out-of-range displacements are refused.

The remaining memory families still return `Resolved.pending` with a
provisional length and always fail emission. Those estimates are not an
encoding or a promise about a future constructor's canonical layout.
-/

namespace Grass.Assembly.Lower.X86

open Grass.Assembly.Syntax
open Grass.ISA.X86
open Grass.ISA.X86.Target

/-! ## Registers

`Instr` has exactly two general-purpose widths (`Sz.w32`, `Sz.w64`): no
8-bit or 16-bit `Sz` exists. An 8-bit or 16-bit spelling is therefore only
ever accepted in the three slots the `Instr` type actually gives them
(`setcc`'s destination, `movzx`/`movsx`'s source); everywhere else, such a
spelling is a plain unrecognized operand and is refused. -/

/-- The first `Gpr` bound to `name` in a name/register table. -/
def lookupGpr : List (String × Gpr) → String → Option Gpr
  | [], _ => none
  | (key, value) :: rest, name => if key = name then some value else lookupGpr rest name

def gpr64Names : List (String × Gpr) :=
  [("rax", .rax), ("rbx", .rbx), ("rcx", .rcx), ("rdx", .rdx), ("rsi", .rsi), ("rdi", .rdi),
    ("rbp", .rbp), ("rsp", .rsp), ("r8", .r8), ("r9", .r9), ("r10", .r10), ("r11", .r11),
    ("r12", .r12), ("r13", .r13), ("r14", .r14), ("r15", .r15)]

def gpr32Names : List (String × Gpr) :=
  [("eax", .rax), ("ebx", .rbx), ("ecx", .rcx), ("edx", .rdx), ("esi", .rsi), ("edi", .rdi),
    ("ebp", .rbp), ("esp", .rsp), ("r8d", .r8), ("r9d", .r9), ("r10d", .r10), ("r11d", .r11),
    ("r12d", .r12), ("r13d", .r13), ("r14d", .r14), ("r15d", .r15)]

/-- 16-bit spellings: only ever consumed as `movzx`/`movsx`'s 16-bit source
(`srcIs16 := true`). There is no ambiguity like the 8-bit high/low split
below, since every 16-bit GPR alias names the low 16 bits of the same
`Gpr` unconditionally. -/
def gpr16Names : List (String × Gpr) :=
  [("ax", .rax), ("bx", .rbx), ("cx", .rcx), ("dx", .rdx), ("si", .rsi), ("di", .rdi),
    ("bp", .rbp), ("sp", .rsp), ("r8w", .r8), ("r9w", .r9), ("r10w", .r10), ("r11w", .r11),
    ("r12w", .r12), ("r13w", .r13), ("r14w", .r14), ("r15w", .r15)]

/-- 8-bit *low-byte* spellings: only ever consumed as `setcc`'s destination
or `movzx`/`movsx`'s 8-bit source (`srcIs16 := false`), since `Instr`
represents that operand as a plain `Gpr` (the byte alias of the full
register), never a `ByteReg`. The legacy high-byte spellings `ah`/`bh`/
`ch`/`dh` are deliberately absent: `Instr` has no way to name bits 15:8 of
`rax`/`rbx`/`rcx`/`rdx` (that is exactly what `Grass.ISA.X86.ByteReg.high`
is for, and no `Instr` constructor here takes a `ByteReg`), so a line that
writes `ah` is refused rather than silently mapped onto `al`. -/
def gpr8LowNames : List (String × Gpr) :=
  [("al", .rax), ("bl", .rbx), ("cl", .rcx), ("dl", .rdx), ("sil", .rsi), ("dil", .rdi),
    ("bpl", .rbp), ("spl", .rsp), ("r8b", .r8), ("r9b", .r9), ("r10b", .r10), ("r11b", .r11),
    ("r12b", .r12), ("r13b", .r13), ("r14b", .r14), ("r15b", .r15)]

/-- A general register operand: 64-bit or 32-bit, whichever the spelling
selects. `none` for every 8/16-bit spelling and every non-register
operand. -/
def registerSized : Operand → Option (Sz × Gpr)
  | .reg name =>
      match lookupGpr gpr64Names name with
      | some r => some (.w64, r)
      | none => (lookupGpr gpr32Names name).map fun r => (.w32, r)
  | _ => none

/-- A bare 64-bit register operand (`push`/`pop`: there is no `push r32` in
64-bit mode). -/
def register64 : Operand → Option Gpr
  | .reg name => lookupGpr gpr64Names name
  | _ => none

/-- An 8-bit low-byte register operand. -/
def registerByte : Operand → Option Gpr
  | .reg name => lookupGpr gpr8LowNames name
  | _ => none

/-- A 16-bit register operand. -/
def registerWord : Operand → Option Gpr
  | .reg name => lookupGpr gpr16Names name
  | _ => none

/-! ## Immediates

Deliberately *not* parameterized by `labels`: `Lowering.size` receives only
an `Env`, so a size computed from a symbol's value cannot depend on a label
address (`Grass/Assembly/Lower/Lowering.lean`'s `Env` docstring). No line in
any of the three spikes uses a label as an immediate operand; every
`Operand.symbol` immediate here is a platform/import constant or a
`sizeof`, both of which `Env` already answers address-independently. -/

/-- The value an operand denotes as an immediate: a literal, a named
constant, or a `sizeof`. -/
def immediate (env : Env) : Operand → Option Int
  | .imm value => some value
  | .symbol name => env.constant name
  | .sizeOf name => (env.sizeOf name).map Int.ofNat
  | _ => none

/-- Whether `value` is representable as a 32/64/8-bit field under the union
of the signed and unsigned conventions (so both `mov eax, -1` and
`mov eax, 0xffffffff` are accepted, and both denote the same bits): the
range `[-2^(bits-1), 2^bits)`. Never truncates — a value outside this range
is refused, not wrapped. -/
def fitsField (bits : Nat) (value : Int) : Bool :=
  decide (-(2 ^ (bits - 1) : Int) ≤ value) && decide (value < (2 : Int) ^ bits)

/-- `value` as a `bits`-wide field, or `none` if it does not fit
(`fitsField`). -/
def toField (bits : Nat) (value : Int) : Option (BitVec bits) :=
  if fitsField bits value then some (BitVec.ofInt bits value) else none

/-- Whether `value` fits the unsigned range `[0, 2^bits)`: used for `movRI32`
used as the zero-extended 64-bit `mov` form, and for shift counts (which are
never negative). -/
def fitsUnsigned (bits : Nat) (value : Int) : Bool :=
  decide (0 ≤ value) && decide (value < (2 : Int) ^ bits)

/-! ## Condition codes -/

/-- `s` with the prefix `pre` removed, or `none` if `s` does not start with
`pre`. -/
def stripPrefix (pre s : String) : Option String :=
  if s.startsWith pre then some (s.drop pre.length).toString else none

/-- The sixteen canonical condition-code mnemonic suffixes
(`Grass.ISA.X86.Target.Cond`'s own spellings), plus the handful of common
synonyms (`z`/`nz` for `e`/`ne`, `c`/`nae`/`nc`/`nb` for `b`/`ae`, `pe`/`po`
for `p`/`np`, `nge`/`nl`/`ng`/`nle` for `l`/`ge`/`le`/`g`) that real x86
assembly uses interchangeably with them. -/
def condOf (suffix : String) : Option Cond :=
  if suffix = "o" then some .o
  else if suffix = "no" then some .no
  else if suffix = "b" || suffix = "c" || suffix = "nae" then some .b
  else if suffix = "ae" || suffix = "nb" || suffix = "nc" then some .ae
  else if suffix = "e" || suffix = "z" then some .e
  else if suffix = "ne" || suffix = "nz" then some .ne
  else if suffix = "be" || suffix = "na" then some .be
  else if suffix = "a" || suffix = "nbe" then some .a
  else if suffix = "s" then some .s
  else if suffix = "ns" then some .ns
  else if suffix = "p" || suffix = "pe" then some .p
  else if suffix = "np" || suffix = "po" then some .np
  else if suffix = "l" || suffix = "nge" then some .l
  else if suffix = "ge" || suffix = "nl" then some .ge
  else if suffix = "le" || suffix = "ng" then some .le
  else if suffix = "g" || suffix = "nle" then some .g
  else none

def jccCondOf (mnemonic : String) : Option Cond := (stripPrefix "j" mnemonic).bind condOf
def setccCondOf (mnemonic : String) : Option Cond := (stripPrefix "set" mnemonic).bind condOf
def cmovccCondOf (mnemonic : String) : Option Cond := (stripPrefix "cmov" mnemonic).bind condOf

/-! ## ALU/shift mnemonic tables -/

def aluOpOf (mnemonic : String) : Option AluOp :=
  if mnemonic = "add" then some .add
  else if mnemonic = "sub" then some .sub
  else if mnemonic = "and" then some .and_
  else if mnemonic = "or" then some .or_
  else if mnemonic = "xor" then some .xor_
  else if mnemonic = "cmp" then some .cmp
  else none

/-! ## Refusals -/

def describe : Operand → String
  | .reg name => name
  | .imm value => toString value
  | .symbol name => name
  | .sizeOf name => "sizeof(" ++ name ++ ")"
  | .mem size base index disp _ =>
      let sizePrefix := match size with
        | some .byte => "byte ptr " | some .word => "word ptr "
        | some .dword => "dword ptr " | some .qword => "qword ptr " | none => ""
      let indexStr := match index with
        | some (name, scale) => "+" ++ name ++ "*" ++ toString scale
        | none => ""
      let dispStr := match disp with
        | .int v => if v = 0 then "" else "+" ++ toString v
        | .symbol name => "+" ++ name
        | .ripRelative name => "rip+" ++ name
      sizePrefix ++ "[" ++ base.getD "" ++ indexStr ++ dispStr ++ "]"
  | .local name => name
  | .localAddress name => name ++ ".addr"

def render (mnemonic : String) (operands : List Operand) : String :=
  mnemonic ++ " " ++ String.intercalate ", " (operands.map describe)

def orRefuse {α : Type} (value : Option α) (message : String) : Except String α :=
  match value with
  | some found => .ok found
  | none => .error message

/-! ## What a line resolves to

`resolve` classifies a `(mnemonic, operands)` pair using only `Env`
(no label addresses, matching `Lowering.size`'s signature): a fully
resolved `Instr`, a branch/call or RIP-relative family (whose *length* is
fixed, but whose final displacement needs the symbol table and this line's
address — supplied later, in `finish`), or a recognized-but-not-yet-
encodable memory-operand shape (`pending`, carrying the length the
eventual encoding will occupy and a message naming which constructor it
needs). `size` and `lower` both go through this one function, so they
cannot disagree about which shape a line is. -/
inductive Resolved where
  | instr (i : Instr)
  | jmp (target : String)
  | jcc (cc : Cond) (target : String)
  | call (target : String)
  | leaRip (dst : Gpr) (target : String)
  | callRip (target : String)
  | pending (length : Nat) (detail : String)

/-- The byte length `Resolved.instr`'s case reads off the real encoder;
every other case already knows its length without needing to build an
`Instr` at all. -/
def Resolved.length : Resolved → Nat
  | .instr i => (encode i).length
  | .jmp _ => 5
  | .jcc _ _ => 6
  | .call _ => 5
  | .leaRip _ _ => 7
  | .callRip _ => 6
  | .pending length _ => length

/-! ## `mov` -/

def lowerMovImm (szD : Sz) (dst : Gpr) (imm : Int) (note : String) : Except String Resolved :=
  match szD with
  | .w32 =>
      match toField 32 imm with
      | some imm32 => .ok (.instr (.movRI32 dst imm32))
      | none => .error ("immediate does not fit 32 bits: " ++ note)
  | .w64 =>
      -- Canonical choice: `movRI32` (5 bytes, zero-extending) whenever the
      -- immediate is representable as a non-negative 32-bit value — this is
      -- exactly the `mov r64, imm` case Encode.lean's `movRI32` execution
      -- already zero-extends correctly — and only `movRI64` (10 bytes, the
      -- full 64-bit immediate) otherwise, i.e. for a negative value or one
      -- that needs bit 32 or above set.
      if fitsUnsigned 32 imm then .ok (.instr (.movRI32 dst (BitVec.ofInt 32 imm)))
      else
        match toField 64 imm with
        | some imm64 => .ok (.instr (.movRI64 dst imm64))
        | none => .error ("immediate does not fit 64 bits: " ++ note)

/-! ## Memory operands

Enabled base forms resolve their displacement in `Env` and become
`Resolved.instr`. RIP forms retain the symbol until `finish`. Unsupported
families remain `Resolved.pending` and cannot satisfy a successful lowering.
-/

/-- Whether a `[base+disp32]` addressing form needs a SIB byte: real x86-64
cannot select `rsp` or `r12` as a ModR/M-direct base (Intel SDM Vol. 2A
Table 2-2), so those two — and only those two — force one. -/
def needsSib (base : Gpr) : Bool := base = Gpr.rsp || base = Gpr.r12

/-- Provisional length for refused base-memory families. Enabled base
forms use the real encoder's mandatory-SIB length instead. -/
def memBaseLen (opcodeBytes : Nat) (wide regExtended : Bool) (base : Gpr) : Nat :=
  (if wide || regExtended || base.isExtended then 1 else 0) + opcodeBytes + 1 +
    (if needsSib base then 1 else 0) + 4

/-- `[rip+disp32]` length: optional REX, `opcodeBytes` opcode bytes,
ModR/M, a mandatory disp32; a RIP-relative operand never uses a SIB byte
(Intel SDM Vol. 2A Table 2-7). -/
def memRipLen (opcodeBytes : Nat) (wide regExtended : Bool) : Nat :=
  (if wide || regExtended then 1 else 0) + opcodeBytes + 1 + 4

/-- Address-shape classification for supported offset syntax. Indexed and
writeback operands are refused. Values and widths are checked separately
before an enabled constructor is emitted. -/
inductive MemShape where
  | rip (name : String)
  | based (base : Gpr)

def memShapeOf : Operand → Option MemShape
  | .mem _ none none (.ripRelative name) .offset => some (.rip name)
  | .mem _ (some base) none (.int _) .offset => (lookupGpr gpr64Names base).map .based
  | .mem _ (some base) none (.symbol _) .offset => (lookupGpr gpr64Names base).map .based
  | .local _ => some (.based Gpr.rsp)
  | .localAddress _ => some (.based Gpr.rsp)
  | _ => none

/-- Signed displacement fields are checked before conversion to their bit pattern. -/
def signed32 (value : Int) : Option (BitVec 32) :=
  if -(2 ^ 31 : Int) ≤ value ∧ value < (2 ^ 31 : Int) then
    some (BitVec.ofInt 32 value)
  else none

/-- Resolve a base displacement from literals, constants, or a declared frame slot. -/
def baseDisplacement (env : Env) (operand : Operand) : Except String (BitVec 32) := do
  let value ← match operand with
    | .mem _ (some _) none (.int value) .offset => .ok value
    | .mem _ (some _) none (.symbol name) .offset =>
        orRefuse (env.constant name) ("unknown displacement constant: " ++ name)
    | .local name | .localAddress name =>
        orRefuse ((env.slot name).map Int.ofNat) ("unknown frame local: " ++ name)
    | _ => .error "unsupported base displacement"
  orRefuse (signed32 value) "base displacement is outside signed disp32 range"

def memSizeBytes : MemSize → Nat
  | .byte => 1
  | .word => 2
  | .dword => 4
  | .qword => 8

/-- Absent bracket widths may be inferred; locals require declared width metadata. -/
def memoryWidth (env : Env) : Operand → Except String (Option Nat)
  | .mem width _ _ _ .offset => .ok (width.map memSizeBytes)
  | .local name => do
      let width ← orRefuse (env.localSize name) ("unknown frame-local width: " ++ name)
      let offset ← orRefuse (env.slot name) ("unknown frame local: " ++ name)
      if offset + width ≤ env.frameBytes then .ok (some width)
      else .error ("local access exceeds the allocated frame: " ++ name)
  | _ => .error "expected a memory value operand"

def checkMemoryWidth (env : Env) (operand : Operand) (bytes : Nat) : Except String Unit := do
  let width ← memoryWidth env operand
  match width with
  | none => .ok ()
  | some actual =>
      if actual = bytes then .ok () else .error "memory and register widths disagree"

def lowerMovRegDest (szD : Sz) (dst : Gpr) (src : Operand) (env : Env) (note : String) :
    Except String Resolved :=
  match registerSized src with
  | some (szS, s) =>
      if szD = szS then .ok (.instr (.movRR szD dst s))
      else .error ("operands mix 32-bit and 64-bit registers: " ++ note)
  | none =>
      match immediate env src with
      | some imm => lowerMovImm szD dst imm note
      | none =>
          match memShapeOf src with
          | some (.rip _) =>
              .ok (.pending (memRipLen 1 szD.isW64 dst.isExtended) (note ++ " — movRMrip"))
          | some (.based base) =>
              do
                checkMemoryWidth env src (if szD.isW64 then 8 else 4)
                let disp ← baseDisplacement env src
                .ok (.instr (.movRM szD dst base disp))
          | none =>
              .error ("mov source is not a register, immediate, or memory operand: " ++ note)

def lowerMovMemDest (shape : MemShape) (dest src : Operand) (env : Env) (note : String) :
    Except String Resolved :=
  match shape with
  | .rip _ => .error ("mov to a RIP-relative destination has no encoding: " ++ note)
  | .based base =>
      match registerSized src with
      | some (szS, s) =>
          .ok (.pending (memBaseLen 1 szS.isW64 s.isExtended base) (note ++ " — movMR"))
      | none =>
          match registerByte src with
          | some s8 => .ok (.pending (memBaseLen 1 false s8.isExtended base) (note ++ " — movMR8"))
          | none =>
              match immediate env src with
              | some imm =>
                  do
                    let width ← memoryWidth env dest
                    let sz ← match width with
                      | some 4 => .ok Sz.w32
                      | some 8 => .ok Sz.w64
                      | _ => .error ("memory immediate store needs a dword or qword width: " ++ note)
                    let disp ← baseDisplacement env dest
                    let field ← orRefuse (if sz.isW64 then signed32 imm else toField 32 imm)
                      ("immediate is not representable by the memory store: " ++ note)
                    .ok (.instr (.movMI32 sz base disp field))
              | none => .error ("mov destination/source shape has no encoding: " ++ note)

def lowerMov (dest src : Operand) (env : Env) (note : String) : Except String Resolved :=
  match registerSized dest with
  | some (szD, dst) => lowerMovRegDest szD dst src env note
  | none =>
      match memShapeOf dest with
      | some shape => lowerMovMemDest shape dest src env note
      | none => .error ("mov destination is not a register or memory operand: " ++ note)

/-! ## `movzx` / `movsx` -/

def lowerMovzx (dest src : Operand) (note : String) : Except String Resolved := do
  let (szD, dst) ← orRefuse (registerSized dest) ("destination is not a register: " ++ note)
  match registerByte src with
  | some s => .ok (.instr (.movzxRR szD dst s false))
  | none =>
      match registerWord src with
      | some s => .ok (.instr (.movzxRR szD dst s true))
      | none =>
          match memShapeOf src with
          | some (.based base) =>
              .ok (.pending (memBaseLen 2 szD.isW64 dst.isExtended base) (note ++ " — movzxRM8"))
          | some (.rip _) =>
              .error ("movzx from a RIP-relative memory operand has no encoding yet: " ++ note)
          | none =>
              .error ("movzx source is not an 8/16-bit register or memory operand: " ++ note)

def lowerMovsx (dest src : Operand) (note : String) : Except String Resolved := do
  let (szD, dst) ← orRefuse (registerSized dest) ("destination is not a register: " ++ note)
  match registerByte src with
  | some s => .ok (.instr (.movsxRR szD dst s false))
  | none =>
      match registerWord src with
      | some s => .ok (.instr (.movsxRR szD dst s true))
      | none =>
          .error ("movsx source is not an 8/16-bit register (no memory form is named yet): "
            ++ note)

/-! ## `lea` -/

def lowerLea (dest src : Operand) (env : Env) (note : String) : Except String Resolved := do
  let dst ← orRefuse (register64 dest) ("lea destination must be a 64-bit register: " ++ note)
  match memShapeOf src with
  | some (.rip name) => .ok (.leaRip dst name)
  | some (.based base) =>
      do
        let disp ← baseDisplacement env src
        .ok (.instr (.leaRM dst base disp))
  | none => .error ("lea source is not a memory operand: " ++ note)

/-! ## ALU (`add sub and or xor cmp`) and `test` -/

def lowerAlu (op : AluOp) (dest src : Operand) (env : Env) (note : String) :
    Except String Resolved :=
  match registerSized dest with
  | some (szD, dst) =>
      match registerSized src with
      | some (szS, s) =>
          if szD = szS then .ok (.instr (.aluRR op szD dst s))
          else .error ("operands mix 32-bit and 64-bit registers: " ++ note)
      | none =>
          match immediate env src with
          | some imm =>
              match toField 32 imm with
              | some imm32 => .ok (.instr (.aluRI op szD dst imm32))
              | none => .error ("immediate does not fit 32 bits: " ++ note)
          | none =>
              match memShapeOf src with
              | some (.rip _) =>
                  .error
                    ("this profile has no RIP-relative arithmetic-source encoding yet: " ++ note)
              | some (.based base) =>
                  .ok (.pending (memBaseLen 1 szD.isW64 dst.isExtended base) (note ++ " — aluRM"))
              | none =>
                  .error ("source is not a register, immediate, or memory operand: " ++ note)
  | none =>
      -- Only `cmp` has a named memory-destination form (`cmpMI32`): no
      -- `aluMR` (a memory *store* direction for `add`/`sub`/...) is named.
      match memShapeOf dest with
      | some (.rip _) => .error ("an arithmetic destination cannot be RIP-relative: " ++ note)
      | some (.based base) =>
          if op = AluOp.cmp then
            match immediate env src with
            | some imm =>
                match toField 32 imm with
                | some _ => .ok (.pending (memBaseLen 1 false false base + 4) (note ++ " — cmpMI32"))
                | none => .error ("immediate does not fit 32 bits: " ++ note)
            | none =>
                .error
                  ("a memory destination needs an immediate source (no aluMR form is named yet): "
                    ++ note)
          else
            .error
              ("a memory destination has no encoding for this operation (no aluMR form is named yet): "
                ++ note)
      | none => .error ("destination is not a register or memory operand: " ++ note)

def lowerTest (a b : Operand) (env : Env) (note : String) : Except String Resolved := do
  let (szA, ra) ← orRefuse (registerSized a) ("first operand is not a register: " ++ note)
  match registerSized b with
  | some (szB, rb) =>
      if szA = szB then .ok (.instr (.testRR szA ra rb))
      else .error ("operands mix 32-bit and 64-bit registers: " ++ note)
  | none =>
      match immediate env b with
      | some imm =>
          match toField 32 imm with
          | some imm32 => .ok (.instr (.testRI szA ra imm32))
          | none => .error ("immediate does not fit 32 bits: " ++ note)
      | none => .error ("second operand is not a register or a resolvable immediate: " ++ note)

/-! ## Shifts, `imul`, unary/binary register forms -/

def lowerShift (op : ShiftOp) (dst imm : Operand) (env : Env) (note : String) :
    Except String Resolved := do
  let (sz, d) ← orRefuse (registerSized dst) ("destination is not a register: " ++ note)
  let value ← orRefuse (immediate env imm) ("not a resolvable immediate: " ++ note)
  if fitsUnsigned 8 value then .ok (.instr (.shiftImm op sz d (BitVec.ofInt 8 value)))
  else .error ("shift amount does not fit 8 bits: " ++ note)

def lowerImul2 (dst src : Operand) (note : String) : Except String Resolved := do
  let (szD, d) ← orRefuse (registerSized dst) ("destination is not a register: " ++ note)
  let (szS, s) ← orRefuse (registerSized src) ("source is not a register: " ++ note)
  if szD = szS then .ok (.instr (.imul2 szD d s))
  else .error ("operands mix 32-bit and 64-bit registers: " ++ note)

def lowerUnaryReg (build : Sz → Gpr → Instr) (operand : Operand) (note : String) :
    Except String Resolved := do
  let (sz, r) ← orRefuse (registerSized operand) ("operand is not a register: " ++ note)
  .ok (.instr (build sz r))

def lowerPushPop (build : Gpr → Instr) (operand : Operand) (note : String) :
    Except String Resolved := do
  let r ← orRefuse (register64 operand) ("operand is not a 64-bit register: " ++ note)
  .ok (.instr (build r))

def lowerSetcc (cc : Cond) (dst : Operand) (note : String) : Except String Resolved := do
  let d ← orRefuse (registerByte dst) ("destination is not an 8-bit register: " ++ note)
  .ok (.instr (.setcc cc d))

def lowerCmovcc (cc : Cond) (dst src : Operand) (note : String) : Except String Resolved := do
  let (szD, d) ← orRefuse (registerSized dst) ("destination is not a register: " ++ note)
  let (szS, s) ← orRefuse (registerSized src) ("source is not a register: " ++ note)
  if szD = szS then .ok (.instr (.cmovcc szD cc d s))
  else .error ("operands mix 32-bit and 64-bit registers: " ++ note)

def lowerXchg (a b : Operand) (note : String) : Except String Resolved := do
  let (szA, ra) ← orRefuse (registerSized a) ("first operand is not a register: " ++ note)
  let (szB, rb) ← orRefuse (registerSized b) ("second operand is not a register: " ++ note)
  if szA = szB then .ok (.instr (.xchgRR szA ra rb))
  else .error ("operands mix 32-bit and 64-bit registers: " ++ note)

/-! ## `call` -/

def lowerCall (operand : Operand) (note : String) : Except String Resolved :=
  match operand with
  | .symbol name => .ok (.call name)
  | _ =>
      match memShapeOf operand with
      | some (.rip name) =>
          match operand with
          | .mem (some .qword) _ _ _ _ | .mem none _ _ _ _ => .ok (.callRip name)
          | _ => .error ("indirect call requires a qword operand: " ++ note)
      | some (.based _) =>
          .error
            ("an indirect call through a base-relative memory operand has no encoding yet: "
              ++ note)
      | none => .error ("call target is not a label or a supported memory operand: " ++ note)

/-! ## The mnemonic dispatch -/

/-- One authored instruction line, classified. -/
def resolve (mnemonic : String) (operands : List Operand) (env : Env) : Except String Resolved :=
  let note := render mnemonic operands
  match mnemonic, operands with
  | "mov", [dest, src] => lowerMov dest src env note
  | "movzx", [dest, src] => lowerMovzx dest src note
  | "movsx", [dest, src] => lowerMovsx dest src note
  | "lea", [dest, src] => lowerLea dest src env note
  | "test", [a, b] => lowerTest a b env note
  | "shl", [dst, imm] => lowerShift .shl dst imm env note
  | "shr", [dst, imm] => lowerShift .shr dst imm env note
  | "sar", [dst, imm] => lowerShift .sar dst imm env note
  | "imul", [dst, src] => lowerImul2 dst src note
  | "inc", [dst] => lowerUnaryReg (fun sz r => .inc sz r) dst note
  | "dec", [dst] => lowerUnaryReg (fun sz r => .dec sz r) dst note
  | "div", [src] => lowerUnaryReg (fun sz r => .div sz r) src note
  | "idiv", [src] => lowerUnaryReg (fun sz r => .idiv sz r) src note
  | "mul", [src] => lowerUnaryReg (fun sz r => .mul sz r) src note
  | "push", [r] => lowerPushPop .push r note
  | "pop", [r] => lowerPushPop .pop r note
  | "xchg", [a, b] => lowerXchg a b note
  | "ret", [] => .ok (.instr .ret)
  | "ud2", [] => .ok (.instr .ud2)
  | "hlt", [] => .ok (.instr .hlt)
  | "nop", [] => .ok (.instr .nop)
  | "syscall", [] => .ok (.instr .syscall)
  | "cdq", [] => .ok (.instr .cdq)
  | "cqo", [] => .ok (.instr .cqo)
  | "jmp", [target] =>
      match target with
      | .symbol name => .ok (.jmp name)
      | _ => .error ("jmp target is not a label: " ++ note)
  | "call", [target] => lowerCall target note
  | "call_local", [target] => lowerCall target note
  | m, [dst, src] =>
      match aluOpOf m with
      | some op => lowerAlu op dst src env note
      | none =>
          match cmovccCondOf m with
          | some cc => lowerCmovcc cc dst src note
          | none => .error ("no x86 encoding for this mnemonic/operand shape: " ++ note)
  | m, [target] =>
      match jccCondOf m with
      | some cc =>
          match target with
          | .symbol name => .ok (.jcc cc name)
          | _ => .error ("branch target is not a label: " ++ note)
      | none =>
          match setccCondOf m with
          | some cc => lowerSetcc cc target note
          | none => .error ("no x86 encoding for this mnemonic/operand shape: " ++ note)
  | _, _ => .error ("no x86 encoding for this mnemonic/operand shape: " ++ note)

/-! ## The instance -/

def size : Line → Env → Except String Nat
  | .label _ _, _ => .ok 0
  | .directive _ _ _, _ => .ok 0
  | .instruction mnemonic operands _, env =>
      match resolve mnemonic operands env with
      | .error message => .error message
      | .ok resolved => .ok resolved.length

/-- A resolved line's final instruction, once the label table and this
line's own address are known: a `Resolved.instr` is already final, a
branch/call resolves its target through `labels` and computes the
displacement from `pc + length` (the address of the *end* of this
instruction — real x86 `rel32`/`rel8` targets are relative to the address of
the following instruction, unlike A64's `cbz`, which is relative to its own
address), and a `pending` line is always refused. -/
def finish (resolved : Resolved) (labels : String → Option Nat) (pc : Nat) :
    Except String (List Grass.ISA.X86.isa.Instr) :=
  match resolved with
  | .instr i => .ok [i]
  | .jmp target =>
      match labels target with
      | none => .error ("branch/call target is not a label: " ++ target)
      | some addr =>
          match toField 32 (Int.ofNat addr - (Int.ofNat pc + 5)) with
          | none => .error ("branch target is out of range: " ++ target)
          | some rel => .ok [.jmpRel32 rel]
  | .jcc cc target =>
      match labels target with
      | none => .error ("branch/call target is not a label: " ++ target)
      | some addr =>
          match toField 32 (Int.ofNat addr - (Int.ofNat pc + 6)) with
          | none => .error ("branch target is out of range: " ++ target)
          | some rel => .ok [.jccRel32 cc rel]
  | .call target =>
      match labels target with
      | none => .error ("branch/call target is not a label: " ++ target)
      | some addr =>
          match toField 32 (Int.ofNat addr - (Int.ofNat pc + 5)) with
          | none => .error ("branch target is out of range: " ++ target)
          | some rel => .ok [.callRel32 rel]
  | .leaRip dst target =>
      match labels target with
      | none => .error ("unknown RIP-relative symbol: " ++ target)
      | some addr =>
          match signed32 (Int.ofNat addr - (Int.ofNat pc + 7)) with
          | none => .error ("RIP-relative target is out of range: " ++ target)
          | some rel => .ok [.leaRip dst rel]
  | .callRip target =>
      match labels target with
      | none => .error ("unknown RIP-relative symbol: " ++ target)
      | some addr =>
          match signed32 (Int.ofNat addr - (Int.ofNat pc + 6)) with
          | none => .error ("RIP-relative target is out of range: " ++ target)
          | some rel => .ok [.callRip rel]
  | .pending _ detail => .error ("memory operand: pending integration (" ++ detail ++ ")")

def lower : Line → Env → (labels : String → Option Nat) → (pc : Nat) →
    Except String (List Grass.ISA.X86.isa.Instr)
  | .label _ _, _, _, _ => .ok []
  | .directive _ _ _, _, _, _ => .ok []
  | .instruction mnemonic operands _, env, labels, pc =>
      match resolve mnemonic operands env with
      | .error message => .error message
      | .ok resolved => finish resolved labels pc

theorem finish_length (resolved : Resolved) (labels : String → Option Nat) (pc : Nat)
    (instrs : List Grass.ISA.X86.isa.Instr) (fin : finish resolved labels pc = .ok instrs) :
    (Grass.ISA.X86.isa.encodeAll instrs).length = resolved.length := by
  cases resolved with
  | instr i =>
      simp only [finish] at fin
      cases fin
      simp [Resolved.length, Grass.ISA.X86.isa, Grass.Target.ISA.encodeAll]
  | jmp target =>
      simp only [finish] at fin
      split at fin
      · simp at fin
      · split at fin
        · simp at fin
        · rename_i rel _
          cases fin
          exact encode_length_jmpRel32 rel
  | jcc cc target =>
      simp only [finish] at fin
      split at fin
      · simp at fin
      · split at fin
        · simp at fin
        · rename_i rel _
          cases fin
          exact encode_length_jccRel32 cc rel
  | call target =>
      simp only [finish] at fin
      split at fin
      · simp at fin
      · split at fin
        · simp at fin
        · rename_i rel _
          cases fin
          exact encode_length_callRel32 rel
  | pending length detail =>
      simp [finish] at fin
  | leaRip dst target =>
      simp only [finish] at fin
      split at fin
      · simp at fin
      · split at fin
        · simp at fin
        · rename_i rel _
          cases fin
          exact encode_length_leaRip dst rel
  | callRip target =>
      simp only [finish] at fin
      split at fin
      · simp at fin
      · split at fin
        · simp at fin
        · rename_i rel _
          cases fin
          exact encode_length_callRip rel

theorem lower_size (line : Line) (env : Env) (labels : String → Option Nat) (pc : Nat)
    (instrs : List Grass.ISA.X86.isa.Instr) (lowered : lower line env labels pc = .ok instrs) :
    size line env = .ok (Grass.ISA.X86.isa.encodeAll instrs).length := by
  cases line with
  | label name annotations =>
      rw [lower] at lowered
      cases lowered
      simp only [size, Grass.Target.ISA.encodeAll_nil, List.length_nil]
  | directive name operands annotations =>
      rw [lower] at lowered
      cases lowered
      simp only [size, Grass.Target.ISA.encodeAll_nil, List.length_nil]
  | instruction mnemonic operands annotations =>
      rw [lower] at lowered
      rw [size]
      cases hres : resolve mnemonic operands env with
      | error message =>
          rw [hres] at lowered
          simp at lowered
      | ok resolved =>
          rw [hres] at lowered
          rw [finish_length resolved labels pc instrs lowered]

/-- The x86-64 instance of the lowering seam. -/
def lowering : Lowering Grass.ISA.X86.isa where
  size := size
  lower := lower
  lower_size := lower_size

end Grass.Assembly.Lower.X86
