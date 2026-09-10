import Tests.ISA.X86.CorpusCommon
import Grass.ISA.X86.Target
import Grass.ISA.X86.RegisterSemantics

/-!
# Seam native-execution corpus

`Tests/ISA/X86/NativeCorpus.lean` generates the 994-case population
`Tools/x86-native/run.py` drives real Windows/x86-64 hardware against, but
every expected register and flag value in it comes from
`Grass.ISA.X86.RegisterSemantics`/`Grass.ISA.X86.ImmediateArithmetic` — the
legacy operand-local semantics `docs/TARGET_SEAMS.md` retires — never from
`Grass.ISA.X86.Target.execInstr`/`step`, which is what `Grass.ISA.X86.isa`
actually wires every platform to. This file re-points that population at the
seam: it mirrors `NativeCorpus.lean`'s four groups and total (450 register
MOV + 420 immediate SUB/CMP + 120 register boundary + 4 Hello operations =
994) exactly, but builds each `Instr`, calls `Grass.ISA.X86.Target.execInstr`
on a from-scratch `State`, and reads the predicted registers and flags back
off the state it returns.

## Two things this file does, not one

1. `generate` (`main`) emits the same TSV shape `NativeCorpus.lean` does —
   label, hex bytes, 16 before/after registers, incoming/expected flags,
   prediction basis — so a future physical campaign can compare it against
   real silicon exactly as `Tools/x86-native/run.py` already knows how to.
   **That campaign cannot run unmodified today**; see "Known blockers" below.
2. `crossCheckLegacy` (also part of `main`) is the honest, hermetic check this
   task asks for and that does not need real hardware at all: for every row,
   it independently computes the *same* instruction's effect through
   `Grass.ISA.X86.RegisterSemantics.evaluate`/`evaluateImmediate` — code
   already reviewed against the Intel SDM (see that module's header) — and
   reports every place the seam's prediction disagrees with it. Two
   independently written implementations of the same instruction set
   disagreeing is real evidence on its own, `docs/VALIDATION.md` §2's
   "compare encoders... where independent tools exist", without needing a
   native trace.

## What actually disagrees: `aluRI`/`testRI` sign-extension at `Sz.w64`

`crossCheckLegacy` finds real mismatches, not zero: `Grass/ISA/X86/Target.lean`
`execInstr`'s `.aluRI`/`.testRI` cases both compute
`UInt64.ofNat imm.toNat` — the immediate's bit pattern **zero-extended** to 64
bits — before applying the operation. Intel's `81 /digit id` encoding (which
is the only encoding `Grass.ISA.X86.Target.Instr.aluRI`/`testRI` ever emits;
see `Grass/ISA/X86/Target/Encode.lean`'s `encodeCore`) sign-extends `imm32` to
64 bits at `REX.W`. `Grass.ISA.X86.RegisterSemantics.evaluateImmediate`
implements that correctly (`BitVec.ofInt 64 immediate.toInt`), so the two
disagree whenever `Sz.w64` and the immediate's bit 31 is set — exactly the two
boundary values `0x80000000`/`0xFFFFFFFF` in `immediates` below, at every
destination and both `sub`/`cmp`. `crossCheckLegacy` reports every such row
below rather than silently emitting a wrong prediction into `generate`'s TSV;
fixing `execInstr` is `Grass/ISA/X86/Target.lean`, out of this file's reach.

## Known blockers to an actual physical campaign

`Tools/x86-native/run.py` (out of `Tests/ISA/X86/`'s scope, not edited here)
would need real changes before it could run against this file's TSV instead
of `NativeCorpus.lean`'s:

- lines 149-150 hardcode the module name `Tests.ISA.X86.NativeCorpus` and the
  path `Tests/ISA/X86/NativeCorpus.lean`.
- `FLAGS_MASK = 0x8D5` (line 13) and `parse_corpus_flags`'s `expected_mask`
  (lines 118-120) require the full CF/PF/AF/ZF/SF/OF mask for every label
  except a `boundary-test-`/`boundary-xor-`/`hello-test-eax-eax` prefix
  allowlist, which then drops only `AF`. The seam has **no `PF`/`AF` field at
  all**, ever, so every row here predicts mask `0x8C1`
  (`CF|ZF|SF|OF`) — a value `expected_mask` does not currently accept for any
  label, so every single row would fail `run.py`'s own
  `require(mask == expected_mask, ...)` unchanged.
- `COVERAGE_SHA256` (line 16) is a hash of this corpus's label/before-register/
  incoming-flags/basis columns; a different `basis` string (this file's
  predictions come from `Instr.encode`+`execInstr`, not
  `Instruction.encoding`+`Instruction.effect`) changes it even though the
  population size (994) and every register value stay identical.

None of this is a defect in the population below — the row count and shapes
match `NativeCorpus.lean` exactly — it is a list of `Tools/` edits the
integrator makes once this file is the one being kept.

## Not attempted here: `Tests/ISA/X86/MachineProbes.lean`

That corpus already has no runner (its harness was "removed on 2026-09-08";
see its own header) and is deliberately not imported by anything, including
`NativeCorpus.lean` (`Tools/x86-native/README.md` explains why). Re-pointing
it at the seam is a separate, larger job: it exercises `AH`/8-bit/16-bit
writes the seam's `Sz` (only `w32`/`w64`) cannot express at all, `BSF` (no
seam `Instr`), and `STC`/`CLC` (no seam `Instr`) — three gaps beyond the
`aluRI`/`testRI` one above, none silently assumed away here.
-/

namespace Grass.Tests.ISA.X86.SeamNative

open Grass.ISA.X86 (Gpr)
open Grass.ISA.X86.Target (Sz AluOp Instr encode execInstr State)
open Grass.Target (StepOutcome)
open Grass.ISA.X86.RegisterSemantics (Kind Flags Effect evaluate evaluateImmediate)
open Grass.ISA.X86.BasicInstructions (Width)
open Grass.Tests.ISA.X86.Corpus (hexBytes hex64)

/-! ## Shared state -/

/-- GPRs the campaign varies; `RSP` is excluded and required unchanged,
matching `Tests/ISA/X86/NativeCorpus.lean`. -/
def registers : List Gpr := Gpr.all.filter (· != .rsp)

/-- The register pattern every non-boundary row starts from: distinct per
register, matching `Tests/ISA/X86/NativeCorpus.lean`'s `initial`, so a
transposed operand or a missed zero-extension is visible the same way. -/
def patternFor (r : Gpr) : BitVec 64 :=
  BitVec.ofNat 64 (0xFEDCBA9876543210 + r.index.val * 0x102030405)

/-- `patternFor`, as the `UInt64` the seam's register file actually holds. -/
def uPatternFor (r : Gpr) : UInt64 := UInt64.ofNat (patternFor r).toNat

/-- The incoming condition flags every row starts from: every seam-modeled
bit set, matching `Tests/ISA/X86/NativeCorpus.lean`'s `initialFlags =
Flags.fromBits 0xAD7` (which also sets `PF`/`AF`; the seam has no field for
either, but the real RFLAGS register a physical campaign loads still needs a
concrete value there). -/
def incomingFlagsWord : UInt64 := 0xAD7

/-- `incomingFlagsWord`, as the six-flag record `RegisterSemantics.evaluate`
takes. -/
def legacyIncomingFlags : Flags Bool := ⟨true, true, true, true, true, true⟩

/-- A from-scratch seam `State`: no memory, no mapped regions, and the
incoming flags above. None of `movRR`/`aluRR`/`aluRI`/`testRR`/`xchgRR` touch
memory, `rip` beyond the length bump `execInstr` always applies, or an
external call, so this is a faithful state for all of them. -/
def buildState (reg : Gpr → UInt64) : State :=
  { reg := reg, rip := 0, cf := true, zf := true, sf := true, ofFlag := true
    mem := fun _ => none, regions := [] }

/-- Run one `Instr` from `before`, returning the resulting register file and
condition flags, or `none` if `execInstr` produced anything other than
`.internal` — which none of the families this file generates ever should. -/
def run (before : Gpr → UInt64) (instr : Instr) :
    Option ((Gpr → UInt64) × Bool × Bool × Bool × Bool) :=
  match execInstr (buildState before) instr (encode instr).length with
  | .internal s => some (s.reg, s.cf, s.zf, s.sf, s.ofFlag)
  | _ => none

def toBV64 (v : UInt64) : BitVec 64 := BitVec.ofNat 64 v.toNat
def toU64 (v : BitVec 64) : UInt64 := UInt64.ofNat v.toNat

/-- `Option Bool` as the SDM already promises it to be here: legacy always
predicts a defined value for `CF`/`ZF`/`SF`/`OF` on every instruction this
corpus generates (only `AF` is ever `none`, for `TEST`/`XOR`, and `AF` is
never compared below). -/
def unwrap (o : Option Bool) : Bool := o.getD false

/-- The `CF|ZF|SF|OF` flags word and mask this corpus's predictions are
stated against — the four condition flags the seam models. `0x8C1 =
0x1 (CF) | 0x40 (ZF) | 0x80 (SF) | 0x800 (OF)`. -/
def flagsMask : UInt64 := 0x8C1

def flagsWord (cf zf sf ofFlag : Bool) : UInt64 :=
  (if cf then 0x1 else 0) ||| (if zf then 0x40 else 0) |||
    (if sf then 0x80 else 0) ||| (if ofFlag then 0x800 else 0)

def hexU64 (v : UInt64) : String := hex64 (toBV64 v)

/-! ## One checked, emittable row -/

/-- Everything one corpus row needs, both to print as a TSV line and to
report against the independent legacy prediction. -/
structure Row where
  /-- The row's label, matching `Tests/ISA/X86/NativeCorpus.lean`'s naming
  where the same case exists there. -/
  label : String
  /-- The seam instruction. -/
  instr : Instr
  /-- The full 16-register file before, in `Gpr.all` (`RAX .. R15`) order. -/
  before : List UInt64
  /-- The full 16-register file the seam predicts after. -/
  after : List UInt64
  /-- The seam's predicted `(CF, ZF, SF, OF)` after. -/
  seamFlags : Bool × Bool × Bool × Bool
  /-- The legacy `RegisterSemantics`/`ImmediateArithmetic` prediction for the
  same instruction and inputs. -/
  legacyDestAfter : UInt64
  /-- The legacy prediction's `(CF, ZF, SF, OF)`. -/
  legacyFlags : Bool × Bool × Bool × Bool
  /-- Which register `legacyDestAfter` is measured on (`none` for `CMP`/`TEST`,
  which write nothing). -/
  destination : Option Gpr
  /-- What produced this row's seam prediction, for the TSV's basis column. -/
  basis : String

/-- Whether the seam's destination write agrees with the independent legacy
prediction. Always `true` when there is no destination (`CMP`/`TEST`). -/
def Row.destAgrees (r : Row) : Bool :=
  match r.destination with
  | none => true
  | some d => decide ((Gpr.all.zip r.after).lookup d = some r.legacyDestAfter)

/-- Whether the seam's `CF/ZF/SF/OF` prediction agrees with the independent
legacy prediction. -/
def Row.flagsAgree (r : Row) : Bool := decide (r.seamFlags = r.legacyFlags)

/-- Build one row for a register-register `Kind` (`mov`/`add`/`sub`/`cmp`/
`test`/`xor`) at one width. -/
def buildRegRow (label : String) (kind : Kind) (width : Width) (sz : Sz)
    (before : Gpr → UInt64) (dst src : Gpr) : Row :=
  let instr : Instr :=
    match kind with
    | .mov => .movRR sz dst src
    | .add => .aluRR .add sz dst src
    | .sub => .aluRR .sub sz dst src
    | .cmp => .aluRR .cmp sz dst src
    | .test => .testRR sz dst src
    | .xor => .aluRR .xor_ sz dst src
  let effect := evaluate kind width (toBV64 (before dst)) (toBV64 (before src)) legacyIncomingFlags
  let destination := if kind = .cmp ∨ kind = .test then none else some dst
  match run before instr with
  | some (afterReg, cf, zf, sf, ofFlag) =>
      { label := label, instr := instr
        before := Gpr.all.map before, after := Gpr.all.map afterReg
        seamFlags := (cf, zf, sf, ofFlag)
        legacyDestAfter := toU64 (effect.destination (toBV64 (before dst)))
        legacyFlags := (unwrap effect.flags.cf, unwrap effect.flags.zf,
          unwrap effect.flags.sf, unwrap effect.flags.of)
        destination := destination
        basis := "Grass.ISA.X86.Target.Instr.encode+execInstr" }
  -- `execInstr` never returns anything but `.internal` for these families; a
  -- non-`.internal` outcome here is itself a finding, reported as an
  -- unconditional mismatch rather than silently discarded.
  | none =>
      { label := label, instr := instr
        before := Gpr.all.map before, after := Gpr.all.map before
        seamFlags := (false, false, false, false)
        legacyDestAfter := toU64 (effect.destination (toBV64 (before dst)))
        legacyFlags := (true, true, true, true)
        destination := destination
        basis := "UNEXPECTED: execInstr did not return .internal" }

/-- Build one row for a `sub`/`cmp` immediate. -/
def buildImmRow (label : String) (kind : Grass.ISA.X86.ImmediateArithmetic.Kind)
    (width : Width) (sz : Sz) (before : Gpr → UInt64) (dst : Gpr) (imm : BitVec 32) : Row :=
  let op : AluOp := match kind with | .sub => .sub | .cmp => .cmp
  let instr : Instr := .aluRI op sz dst imm
  let effect := evaluateImmediate kind width (toBV64 (before dst)) (.i32 imm) legacyIncomingFlags
  let destination := if kind = .cmp then none else some dst
  match run before instr with
  | some (afterReg, cf, zf, sf, ofFlag) =>
      { label := label, instr := instr
        before := Gpr.all.map before, after := Gpr.all.map afterReg
        seamFlags := (cf, zf, sf, ofFlag)
        legacyDestAfter := toU64 (effect.destination (toBV64 (before dst)))
        legacyFlags := (unwrap effect.flags.cf, unwrap effect.flags.zf,
          unwrap effect.flags.sf, unwrap effect.flags.of)
        destination := destination
        basis := "Grass.ISA.X86.Target.Instr.encode+execInstr (aluRI, imm32)" }
  | none =>
      { label := label, instr := instr
        before := Gpr.all.map before, after := Gpr.all.map before
        seamFlags := (false, false, false, false)
        legacyDestAfter := toU64 (effect.destination (toBV64 (before dst)))
        legacyFlags := (true, true, true, true)
        destination := destination
        basis := "UNEXPECTED: execInstr did not return .internal" }

/-! ## The four groups, mirroring `Tests/ISA/X86/NativeCorpus.lean` -/

def widths : List (Width × Sz) := [(.w32, .w32), (.w64, .w64)]

def widthText : Sz → String
  | .w32 => "w32"
  | .w64 => "w64"

def kindText : Kind → String
  | .mov => "mov" | .add => "add" | .sub => "sub"
  | .cmp => "cmp" | .test => "test" | .xor => "xor"

/-- 450 cases: every pair among the 15 non-`RSP` GPRs, both widths. -/
def movMatrixRows : List Row :=
  registers.flatMap fun dst => registers.flatMap fun src => widths.map fun (w, sz) =>
    buildRegRow s!"mov-{dst.index.val}-{src.index.val}-{widthText sz}" .mov w sz uPatternFor dst src

/-- The seven immediate values this corpus tests, as plain 32-bit patterns.
`NativeCorpus.lean` splits its analogous seven values across the imm8 (`83`)
and imm32 (`81`) encodings; the seam's `aluRI` only ever emits `81`
(`Grass/ISA/X86/Target/Encode.lean`), so every value here is a literal imm32
pattern instead. `0x80000000`/`0xFFFFFFFF` are exactly the two whose bit 31
is set — the values that expose the `Sz.w64` sign-extension gap documented
above. -/
def immediates : List (BitVec 32) := [0, 127, 128, 255, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]

/-- 420 cases: 15 destinations, both widths, both `sub`/`cmp`, all seven
immediates. -/
def immRows : List Row :=
  registers.flatMap fun dst => widths.flatMap fun (w, sz) =>
    ([Grass.ISA.X86.ImmediateArithmetic.Kind.sub, .cmp]).flatMap fun kind =>
      immediates.map fun imm =>
        buildImmRow s!"arith-{dst.index.val}-{widthText sz}-{repr kind}-{repr imm}"
          kind w sz uPatternFor dst imm

/-- The ten `(destination, source)` boundary pairs per width, verbatim from
`Tests/ISA/X86/NativeCorpus.lean`'s `boundaryValues`. -/
def boundaryValues : Sz → List (Nat × Nat)
  | .w32 => [(0, 0), (0, 1), (1, 1), (15, 1), (16, 1), (0xFFFFFFFF, 1),
             (0x7FFFFFFF, 1), (0x80000000, 1), (0x7FFFFFFF, 0x7FFFFFFF),
             (0x80000000, 0x80000000)]
  | .w64 => [(0, 0), (0, 1), (1, 1), (15, 1), (16, 1), (0xFFFFFFFFFFFFFFFF, 1),
             (0x7FFFFFFFFFFFFFFF, 1), (0x8000000000000000, 1),
             (0x7FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF),
             (0x8000000000000000, 0x8000000000000000)]

/-- The full register file for one boundary case: every register at its
ordinary pattern except `RAX`/`RCX`, which carry the boundary destination and
source, tagged with a distinguishing high half at `w32` exactly as
`Tests/ISA/X86/NativeCorpus.lean`'s `boundaryState` does. -/
def boundaryReg (sz : Sz) (destination source : Nat) : Gpr → UInt64
  | .rax => UInt64.ofNat (match sz with
      | .w32 => 0xA5A5A5A500000000 + destination
      | .w64 => destination)
  | .rcx => UInt64.ofNat (match sz with
      | .w32 => 0x5A5A5A5A00000000 + source
      | .w64 => source)
  | r => uPatternFor r

/-- 120 cases: all six register `Kind`s, both widths, all ten boundary
pairs, always on `RAX`/`RCX`. -/
def boundaryRows : List Row :=
  ([Kind.mov, .add, .sub, .cmp, .test, .xor]).flatMap fun kind =>
    widths.flatMap fun (w, sz) =>
      ((boundaryValues sz).zipIdx).map fun ((destination, source), index) =>
        buildRegRow s!"boundary-{kindText kind}-{widthText sz}-{index}" kind w sz
          (boundaryReg sz destination source) .rax .rcx

/-- The four exact operand selections `NativeCorpus.lean` names as the
current Hello lowering path. -/
def helloRows : List Row :=
  [ buildRegRow "hello-test-eax-eax" .test .w32 .w32 uPatternFor .rax .rax
  , buildRegRow "hello-cmp-eax-r14d" .cmp .w32 .w32 uPatternFor .rax .r14
  , buildRegRow "hello-add-r13-rax" .add .w64 .w64 uPatternFor .r13 .rax
  , buildRegRow "hello-sub-r14d-eax" .sub .w32 .w32 uPatternFor .r14 .rax ]

/-- The whole corpus: 450 + 420 + 120 + 4 = 994, matching
`Tests/ISA/X86/NativeCorpus.lean`'s population exactly. -/
def corpus : List Row := movMatrixRows ++ immRows ++ boundaryRows ++ helloRows

/-! ## `generate`: the TSV, for a future physical campaign -/

def csv16 (values : List UInt64) : String :=
  String.intercalate "," (values.zipIdx.map fun (v, i) => if i == 4 then "-" else hexU64 v)

/-- Print one row as `label⟨TAB⟩bytes⟨TAB⟩before⟨TAB⟩after⟨TAB⟩flagsIn⟨TAB⟩
flagsOut⟨TAB⟩basis`, the same shape `Tests/ISA/X86/NativeCorpus.lean` emits. -/
def emitRow (r : Row) : IO Unit :=
  let (cf, zf, sf, ofFlag) := r.seamFlags
  IO.println (String.intercalate "\t"
    [ r.label, hexBytes ((encode r.instr).map UInt8.toBitVec), csv16 r.before, csv16 r.after,
      hexU64 incomingFlagsWord, hexU64 (flagsWord cf zf sf ofFlag) ++ "/" ++ hexU64 flagsMask,
      r.basis ])

def generate : IO Unit := do
  for r in corpus do emitRow r

/-! ## `crossCheckLegacy`: the hermetic, decidable differential -/

def crossCheckLegacy : IO Unit := do
  let mismatches := corpus.filter fun r => !r.destAgrees || !r.flagsAgree
  IO.eprintln "== Seam native-execution cross-check (Tests/ISA/X86/SeamNativeCorpus.lean) =="
  IO.eprintln s!"corpus rows: {corpus.length} (450 mov + 420 immediate + 120 boundary + 4 hello)"
  IO.eprintln s!"checked against RegisterSemantics/ImmediateArithmetic: {corpus.length}"
  IO.eprintln "unsupported (no seam Instr): 0 -- every NativeCorpus.lean shape is a seam Instr"
  if mismatches.isEmpty then
    IO.eprintln "cross-check: 994 agree, 0 mismatches"
  else
    IO.eprintln s!"cross-check: {corpus.length - mismatches.length} agree, \
      {mismatches.length} MISMATCH"
    for r in mismatches do
      IO.eprintln s!"MISMATCH {r.label} ({r.basis})"
      IO.eprintln s!"  instr:          {reprStr r.instr}"
      if !r.destAgrees then
        let seamDest := match r.destination with
          | some d => hexU64 ((Gpr.all.zip r.after).lookup d |>.getD 0)
          | none => "(no destination)"
        IO.eprintln s!"  seam dest:      {seamDest}"
        IO.eprintln s!"  legacy dest:    {hexU64 r.legacyDestAfter}"
      if !r.flagsAgree then
        let (scf, szf, ssf, sof) := r.seamFlags
        let (lcf, lzf, lsf, lof) := r.legacyFlags
        IO.eprintln s!"  seam flags   cf={scf} zf={szf} sf={ssf} of={sof}"
        IO.eprintln s!"  legacy flags cf={lcf} zf={lzf} sf={lsf} of={lof}"

end Grass.Tests.ISA.X86.SeamNative

/-- Top level rather than in the namespace because `lake env lean --run` looks
for `main` there. `generate`'s TSV goes to stdout, exactly like
`Tests/ISA/X86/NativeCorpus.lean`'s, so a future campaign can still pipe this
file's output the same way; `crossCheckLegacy`'s report goes to stderr so it
never corrupts that TSV, and exits nonzero on any mismatch so this file fails
`lake build`'s consumer loudly rather than passing by construction. -/
def main : IO Unit := do
  Grass.Tests.ISA.X86.SeamNative.generate
  Grass.Tests.ISA.X86.SeamNative.crossCheckLegacy
  let mismatches := (Grass.Tests.ISA.X86.SeamNative.corpus.filter fun r =>
    !r.destAgrees || !r.flagsAgree)
  if !mismatches.isEmpty then IO.Process.exit 1
