import Tests.ISA.X86.CorpusCommon

/-!
# Physical probe corpus

`docs/VALIDATION.md` §2 layer 3: "Physical probes: execute generated
instruction/API cases on named CPU/OS/GPU profiles and compare complete declared
effects."

Every other check in this tree compares Grass against a *document* or against
another *tool*. This one compares it against the processor. It is the only layer
that can settle a question the manuals leave ambiguous and NASM cannot see —
and there are such questions open right now.

## What the model predicts

The expected register file is not written out by hand. It is computed by
`Grass.ISA.X86.writeBack`, the operand-size rule this profile models, so a probe
that disagrees is a disagreement with *the model* rather than with a second
hand-written table that could drift from it.

`docs/VALIDATION.md` §2 is explicit that this cuts both ways: "Tools and
hardware are fallible oracles. Disagreement is preserved as a finding; majority
vote does not establish truth." A failing probe is a finding against Grass, or
against the harness, or a genuine erratum. It is resolved by reading the manual.

## The exceptions this corpus exists to decide

Two reviewers flagged that `Rules.registerWriteExtension` states the 32-bit
zero-extension rule without qualification, and named cases where it is claimed
not to hold. The manuals settle these; the manuals are also exactly what this
corpus cannot currently reach, since `Grass/ISA/X86/Sources.lean` records the
AMD APM as unretrievable and no anchor is confirmed. So the probes decide them
on silicon in the meantime:

- **`0x90` is `NOP`, not `xchg eax, eax`.** The one-byte form does not write
  `RAX` at all, so the zero-extension rule must not apply to it. `87 C0` is the
  same architectural operation encoded through ModR/M, and *does* zero-extend.
  Running both against the same initial state separates them.
- **`41 90` is a real `XCHG`,** because `REX.B` makes the opcode-embedded
  register `r8d` rather than `eax`, so it is no longer the degenerate case.
- **A high-byte write goes to bits 15:8.** `writeBack` is indexed by `Width`,
  which cannot distinguish `AH` from `AL`, so the model has no prediction here
  and the probe records what the processor does. That gap is the finding.

Each probe carrying an expectation the general rule would get wrong is marked,
and the runner reports those separately from ordinary agreement.

## Isolation

An instruction under test can fault. `docs/VALIDATION.md` §4 requires probe
processes to be isolated when faults or hangs are possible, so
`Tools/x86-machine-probe.py` runs each probe in a child process. Windows sets a
crashed child's exit code to the NTSTATUS, which means the fault class is
reported rather than lost — a probe that raises `#UD` is data, not a crash.

Ring 0 behaviour is out of reach from a user-mode process and is not attempted.
-/

namespace Grass.Tests.ISA.X86.Probe

open Grass.Std.Logical Grass.ISA.X86 Grass.Tests.ISA.X86.Corpus

/-- A recognisable initial value for every register: `0xFFFF_FFFF_FFFF_FFFF`.

All ones is the value that makes a zero-extension visible. With a small initial
value, a 32-bit write that wrongly preserved the upper half would produce the
same answer as one that correctly cleared it. -/
def allOnes : BitVec 64 := 0xFFFFFFFFFFFFFFFF

/-- The RFLAGS value every probe starts from: bit 1 reserved-set, IF set.

A definite value rather than whatever the interpreter left behind, so that a
flag result is a fact about the instruction and not about the harness. -/
def standardFlags : BitVec 64 := 0x202

/-- The initial register file: every register all ones. -/
def initialState : List (BitVec 64) := List.replicate 16 allOnes

/-- Replace one register in a state, by encoding-order index. -/
def setReg (state : List (BitVec 64)) (r : Gpr) (v : BitVec 64) : List (BitVec 64) :=
  state.set r.index.val v

/-- The state after writing `v` at width `w` into `r`, as `writeBack` predicts.

This is the whole point of the corpus: the prediction comes from the modeled
rule, not from a second table written beside it. -/
def predictWrite (state : List (BitVec 64)) (r : Gpr) (w : Width)
    (v : BitVec w.bits) : List (BitVec 64) :=
  setReg state r (writeBack w (state.getD r.index.val 0) v)

/-- One probe: what to run, from what state, and what the model says happens. -/
structure Probe where
  /-- What this probe is testing. -/
  label : String
  /-- The instruction bytes to execute. -/
  bytes : ByteSeq
  /-- The register file before, in encoding order. -/
  before : List (BitVec 64)
  /-- The register file the model predicts after. -/
  after : List (BitVec 64)
  /-- The RFLAGS value loaded before the instruction runs.

  Fixed rather than inherited. A reviewer found the incoming flags were
  whatever the interpreter happened to leave -- `0x246`, with ZF already set --
  so a result like "XOR set ZF" was unfalsifiable even in principle. -/
  flagsIn : BitVec 64
  /-- The RFLAGS the model predicts, where the model has a prediction.

  `none` for almost everything, because Grass does not model flags yet. That is
  an **open obligation**, not a claim that these instructions leave flags alone:
  the runner reports the value it measured and compares nothing. The two probes
  that do set this are the ones whose flag effect is certain from the incoming
  value alone, so the mechanism is exercised rather than dead. -/
  flagsOut : Option (BitVec 64)
  /-- Whether the prediction is one the general operand-size rule would get
  wrong, so the runner can report it separately. -/
  isException : Bool
  /-- What a reader needs to know to interpret a disagreement. -/
  note : String

/-- `mov r32, imm32` for a chosen register: the zero-extension case. -/
def movR32 (r : Gpr) : Probe :=
  let v : BitVec 32 := 0x11223344
  { label := "mov " ++ nasmName32 r ++ ", 0x11223344"
    bytes := (movRegImm32 r v).toBytes
    before := initialState
    after := predictWrite initialState r .w32 v
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "32-bit write: bits 63:32 must become zero (writeBack.w32_clears_high)" }

/--
`0x90` with every register all ones.

The model's general rule would call this `xchg eax, eax` and predict `RAX`
zero-extended to `0x00000000FFFFFFFF`. The architecture says `0x90` without
`REX.B` is `NOP`, which writes nothing, so the prediction here is that `RAX` is
**unchanged**. If the processor agrees, `Rules.registerWriteExtension` needs the
carve-out; if it does not, the reviewers who raised this were wrong.
-/
def nopByte : Probe :=
  { label := "0x90 (one-byte NOP, not xchg eax/eax)"
    bytes := [0x90]
    before := initialState
    after := initialState
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := true
    note := "expects RAX unchanged; the unqualified 32-bit rule would predict "
              ++ "0x00000000ffffffff" }

/-- `87 C0` — `xchg eax, eax` through ModR/M, which *is* a 32-bit write. -/
def xchgEaxEax : Probe :=
  { label := "87 C0 (xchg eax, eax via ModR/M)"
    bytes := [0x87, 0xC0]
    before := initialState
    after := predictWrite initialState .rax .w32 0xFFFFFFFF
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "same operation as 0x90 but a real 32-bit write, so it zero-extends" }

/-- `41 90` — `REX.B` makes the opcode register `r8d`, so this is a genuine
exchange and both registers take 32-bit writes. -/
def xchgR8dEax : Probe :=
  { label := "41 90 (xchg r8d, eax -- REX.B, so not the NOP case)"
    bytes := [0x41, 0x90]
    before := initialState
    after := predictWrite (predictWrite initialState .rax .w32 0xFFFFFFFF)
               .r8 .w32 0xFFFFFFFF
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "REX.B makes this a real xchg; both destinations zero-extend" }

/-- `B4 imm8` — `mov ah, imm8`, which writes bits 15:8.

The model has no prediction: `writeBack` is indexed by `Width`, which cannot
tell `AH` from `AL`. The stated expectation is the architecture's, and the probe
exists to record that the model cannot produce it. -/
def movAh : Probe :=
  { label := "B4 5A (mov ah, 0x5a -- high-byte register)"
    bytes := [0xB4, 0x5A]
    before := initialState
    after := setReg initialState .rax 0xFFFFFFFFFFFF5AFF
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := true
    note := "writes bits 15:8 and preserves 7:0; writeBack .w8 writes 7:0, so "
              ++ "the model cannot express this case at all" }

/-- `B0 imm8` — `mov al, imm8`, the low-byte case the model does cover. -/
def movAl : Probe :=
  { label := "B0 5A (mov al, 0x5a -- low-byte register)"
    bytes := [0xB0, 0x5A]
    before := initialState
    after := predictWrite initialState .rax .w8 0x5A
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "8-bit write: bits 63:8 preserved (writeBack.w8_preserves_high)" }

/-- `66 B8 imm16` — `mov ax, imm16`, the 16-bit case. -/
def movAx : Probe :=
  { label := "66 B8 5A5A (mov ax, 0x5a5a -- 16-bit operand)"
    bytes := [0x66, 0xB8, 0x5A, 0x5A]
    before := initialState
    after := predictWrite initialState .rax .w16 0x5A5A
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "16-bit write: bits 63:16 preserved (writeBack.w16_preserves_high)" }

/--
`48 C7 C0 imm32` — `mov rax, imm32` sign-extended, the 64-bit-destination case.

A reviewer measured that `writeBack .w64` had **zero** probe coverage: mutating
it to preserve the upper half instead of replacing the register changed no
corpus row and was caught by no probe. "A 64-bit destination replaces the
register" is one of the three things `Rules.registerWriteExtension` states, and
until this row it was the one settled by nothing — not by a probe, not by a
confirmed anchor.

The immediate is sign-extended to 64 bits, so `0x11223344` gives exactly
`0x0000000011223344` and a model that preserved the upper half would give
`0xFFFFFFFF11223344`.
-/
def movR64 : Probe :=
  { label := "48 C7 C0 11223344 (mov rax, imm32 sign-extended -- 64-bit dest)"
    bytes := [0x48, 0xC7, 0xC0, 0x44, 0x33, 0x22, 0x11]
    before := initialState
    after := predictWrite initialState .rax .w64 0x0000000011223344
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "64-bit write: replaces the register (writeBack.w64_independent)" }

/--
`0F BC C1` — `bsf eax, ecx` with a zero source.

The third carve-out in `Rules.registerWriteExtension`, and the only one that was
asserted with no evidence of any kind: no probe, no confirmed anchor, and by the
rule's own comment the case "where the vendors are reported to differ". Intel
documents the destination as undefined for a zero source; AMD is reported to
leave it unmodified.

If the destination is genuinely not written, the 32-bit rule does not reach it
and bits 63:32 stay set — which is what this probe expects. A processor that
zero-extended anyway would report `0x00000000ffffffff` and the carve-out would
be wrong on this part.
-/
def bsfZeroSource : Probe :=
  { label := "0F BC C1 (bsf eax, ecx with ecx = 0 -- undefined destination)"
    bytes := [0x0F, 0xBC, 0xC1]
    before := setReg initialState .rcx 0
    after := setReg initialState .rcx 0
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := true
    note := "expects RAX entirely unchanged, so no 32-bit write occurred; the "
              ++ "unqualified rule would predict 0x00000000ffffffff" }

/-- `66 B8` and `B0` cover 16- and 8-bit writes with one row each, which a
reviewer noted makes a typo and a broken model the same evidence. `movAxOther`
and `movAlOther` write a second, different value so that a model that happened
to agree on one constant does not agree on both. -/
def movAxOther : Probe :=
  { label := "66 B8 FFFF (mov ax, 0xffff -- 16-bit, all-ones payload)"
    bytes := [0x66, 0xB8, 0xFF, 0xFF]
    before := setReg initialState .rax 0
    after := predictWrite (setReg initialState .rax 0) .rax .w16 0xFFFF
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "16-bit write into a zeroed register: bits 63:16 stay zero" }

/-- The 8-bit counterpart, also from a zeroed register. -/
def movAlOther : Probe :=
  { label := "B0 FF (mov al, 0xff -- 8-bit, all-ones payload)"
    bytes := [0xB0, 0xFF]
    before := setReg initialState .rax 0
    after := predictWrite (setReg initialState .rax 0) .rax .w8 0xFF
    flagsIn := standardFlags
    flagsOut := Option.none
    isException := false
    note := "8-bit write into a zeroed register: bits 63:8 stay zero" }

/-- `F9` — `STC`, which sets CF and leaves the other flags alone.

One of the two probes whose flag effect is certain from `standardFlags` alone,
so the flags comparison is exercised rather than carried dead. -/
def stc : Probe :=
  { label := "F9 (stc -- sets CF)"
    bytes := [0xF9]
    before := initialState
    after := initialState
    flagsIn := standardFlags
    flagsOut := some (standardFlags ||| 1)
    isException := false
    note := "sets CF and touches no register" }

/-- `F8` — `CLC`, which clears CF. Starting from `standardFlags`, where CF is
already clear, the flags come back unchanged. -/
def clc : Probe :=
  { label := "F8 (clc -- clears CF)"
    bytes := [0xF8]
    before := initialState
    after := initialState
    flagsIn := standardFlags ||| 1
    flagsOut := some standardFlags
    isException := false
    note := "clears CF; started with CF set so the change is visible" }

/-- The whole corpus.

`movR32` runs over every register, which also exercises the opcode-embedded
register field and its `REX.B` extension — the third place a register number can
appear, and one no other corpus covers. -/
def corpus : List Probe :=
  ((Gpr.all.filter (fun r => r != .rsp)).map movR32)
    ++ [nopByte, xchgEaxEax, xchgR8dEax, movAh, movAl, movAx,
        movR64, bsfZeroSource, movAxOther, movAlOther, stc, clc]

end Grass.Tests.ISA.X86.Probe

/-- Emit the corpus as `label TAB bytes TAB before TAB after TAB exception TAB note`,
with register files as comma-separated hex in encoding order. -/
def main : IO Unit := do
  let hex64 (v : BitVec 64) : String :=
    Grass.Tests.ISA.X86.Corpus.hexBytes
      [BitVec.extractLsb' 56 8 v, BitVec.extractLsb' 48 8 v,
       BitVec.extractLsb' 40 8 v, BitVec.extractLsb' 32 8 v,
       BitVec.extractLsb' 24 8 v, BitVec.extractLsb' 16 8 v,
       BitVec.extractLsb' 8 8 v, BitVec.extractLsb' 0 8 v]
  for p in Grass.Tests.ISA.X86.Probe.corpus do
    let before := String.intercalate "," (p.before.map hex64)
    let after := String.intercalate "," (p.after.map hex64)
    let flagsOut := match p.flagsOut with
      | some v => hex64 v
      | Option.none => "-"
    IO.println (p.label ++ "\t" ++ Grass.Tests.ISA.X86.Corpus.hexBytes p.bytes ++
      "\t" ++ before ++ "\t" ++ after ++ "\t" ++
      (if p.isException then "exception" else "rule") ++ "\t" ++ p.note ++
      "\t" ++ hex64 p.flagsIn ++ "\t" ++ flagsOut)
