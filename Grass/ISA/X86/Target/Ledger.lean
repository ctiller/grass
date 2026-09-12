import Grass.ISA.X86.Ledger
import Grass.ISA.X86.Sources

/-!
# The seam ISA's trust ledger

`docs/FOUNDATION.md` law 1: "No semantic invention: ISA/API behavior requires
an authoritative citation." `docs/DECISIONS.md` 21: "All instruction/API
behavior has vendor/standard citations ... and a per-profile trust ledger."
`docs/DECISIONS.md` 15 requires the dual Intel/AMD citation `docs/INSTRUCTIONS.md`
§7 and `Grass/ISA/X86/DualCitation.lean` mechanize.

Commit `6a7ea03a` deleted `Tests/ISA/X86/LedgerAudit.lean`, which enforced this
for the legacy decoder's subjects (`Grass/ISA/X86/Profile.lean`'s
`commonProfileLedger`). Neither that ledger nor its deleted audit ever named
anything in `Grass/ISA/X86/Target/Encode.lean` (`Instr`, `encode`, `decode`) or
`Grass/ISA/X86/Target.lean` (`execInstr`, `step`, `initial`): the seam is a
separate, later-written instruction set with its own 38-constructor `Instr`
and its own execution semantics, and it was never entered in any ledger. This
module is that ledger, in the shape `Grass/ISA/X86/Ledger.lean` already
defines and enforces -- `CommonRule`, `DualCitation`, `Citation` are reused
unchanged, not forked, per this module's task.

`Tests/ISA/X86/SeamLedgerAudit.lean` is the companion coverage ratchet: it
enumerates every constructor of `Instr` and every top-level declaration of
`Grass.ISA.X86.Target` (the file `Grass/ISA/X86/Target.lean`) and requires each
to be cited here, explicitly waived as carrying no external behaviour, or
listed as an explicit, only-shrinking debt. `docs/VALIDATION.md` §6 and §7 own
that ledger/ratchet split; this file is the citation half.

## What is actually cited here, and why most of it is not

Of `Instr`'s 38 constructors, eight have a citation below: `movRR`, `movRI32`,
`movRI64` (MOV) and `testRR`, `testRI` (TEST), whose Intel/AMD printed-page
anchors are already recorded in `docs/REFERENCES.md`'s "Register semantics
anchors", plus `syscall`, `ud2`, `hlt`, whose defining behaviour is a single
well-known instruction-reference entry. Five more subjects are execution
facts `execInstr` relies on that are not about one instruction: the ADD/SUB
CF/OF definitions (`addSubFlags`), the Jcc condition table (`condHolds`),
32-bit register-write zero-extension (`regWrite`), and RIP-relative
addressing measured from the next instruction, split into the general
addressing fact (`execInstr.ripRelativeNextInstruction`, since no single named
declaration owns "next instruction" -- it is the `next` let-binding recomputed
at every `execInstr` case) and the SYSCALL-specific register clobber set
(`execInstr.syscallClobbers`, since `execInstr` delegates the actual clobber
list to a platform's `NativeReturn.clobbers` and never states rcx/r11 itself).

The remaining 30 `Instr` constructors (`movzxRR`, `movsxRR`, `aluRR`, `aluRI`,
`shiftImm`, `imul2`, `inc`, `dec`, `push`, `pop`, `callRel32`, `ret`,
`jmpRel32`, `jmpRel8`, `jccRel32`, `jccRel8`, `nop`, `cdq`, `cqo`, `div`,
`idiv`, `mul`, `setcc`, `cmovcc`, `xchgRR`, `movRM`, `movMI32`, `leaRM`,
`leaRip`, `callRip`) and several of `Target.lean`'s own
declarations genuinely model external behaviour and have no citation yet.
That debt is not hidden here: `Tests/ISA/X86/SeamLedgerAudit.lean` lists it
explicitly as `owed`, per declaration, with the reason no anchor was used.
`aluRR`/`aluRI` are the clearest case -- `docs/REFERENCES.md` gives inspected
pages for four of the six ALU mnemonics each constructor covers (ADD, SUB,
XOR, CMP) but not the other two (OR, AND), so citing the constructor as if
fully covered would overstate what has actually been checked; it is owed
rather than half-cited.

Every citation below has `basis := .assertedPendingConfirmation` and, unless
noted, `confirmed := none`: nobody has yet followed these particular anchors
inside a manual and recorded the date on `Citation.confirmed`, which is an
honest and expected intermediate state, not a `WellFormed` failure (see
`Grass/ISA/X86/Citation.lean`). Two subjects are the deliberate exception:
`regWrite` and `execInstr.ripRelativeNextInstruction` restate a fact
`Grass/ISA/X86/Profile.lean`'s `registerWriteExtension`/`ripRelativeForm`
already has a *confirmed* Intel anchor for (the same manual, the same
section), and that confirmation is reused honestly on the Intel side rather
than re-marked unconfirmed for no reason; their AMD sides are not reused
because this module cites different AMD sections than those rules do (see
each rule's docstring), which nobody has opened.

No document is invented. Every citation below is filed against
`Grass.ISA.X86.Vendor.document`, exactly `intelSdm092` and `amd64Apm410` from
`Grass/ISA/X86/Sources.lean` -- the same two `SourceDocument`s
`docs/AMD_SOURCE_MIGRATION.md` and `docs/DECISIONS.md` 15 pin the whole common
profile to.

## Pending rows for the concurrently-added memory-operand family

`Grass/ISA/X86/Target/Encode.lean` and `Grass/ISA/X86/Target.lean` are being
extended concurrently with memory-operand constructors -- `movRM`, `movMR`,
`movMI32`, `movzxRM8`, `movMR8`, `leaRM`, `leaRip`, `movRMrip`, `callRip`,
`cmpMI32`, `aluRM` -- in stages. Five forms (`movRM`, `movMI32`, `leaRM`,
`leaRip`, `callRip`) now exist and are explicitly owed by the coverage gate.
The other six still have no real constructor subject. `PendingRow` below
remains an unaudited citation worklist, not part of `Ledger` or consulted by
`Covers`/`Accounts`. Entries for existing constructors need formal source
enrollment; entries for absent constructors also need a real declaration
before Gate A can accept a corresponding ledger subject.
-/

namespace Grass.ISA.X86.Target

open Grass.Core Grass.Cite Grass.ISA.X86

-- Kernel decision checks traverse the detailed source locators below, as in
-- `Grass/ISA/X86/Profile.lean`.
set_option maxRecDepth 2048

/-! ## Subjects

Each subject names either a real `Instr` constructor (spelled to match its
fully qualified constructor name exactly, so `Tests/ISA/X86/SeamLedgerAudit.lean`'s
Gate A resolves it with zero discriminator segments) or a real top-level
`Target.lean` declaration, optionally with one discriminator segment for a
fact that declaration carries but does not itself get an entire named
declaration for (`execInstr.ripRelativeNextInstruction`,
`execInstr.syscallClobbers`), following the convention
`Grass/ISA/X86/Profile.lean` already uses for `decodeMem.ripRelative` and its
siblings.
-/

namespace Subject

/-- `Instr.movRR` -- `MOV r/m, r`, register-direct. -/
def movRR : Name := ⟨"Grass.ISA.X86.Target.Instr.movRR"⟩
/-- `Instr.movRI32` -- `MOV r32, imm32`. -/
def movRI32 : Name := ⟨"Grass.ISA.X86.Target.Instr.movRI32"⟩
/-- `Instr.movRI64` -- `MOV r64, imm64`. -/
def movRI64 : Name := ⟨"Grass.ISA.X86.Target.Instr.movRI64"⟩
/-- `Instr.testRR` -- `TEST r/m, r`. -/
def testRR : Name := ⟨"Grass.ISA.X86.Target.Instr.testRR"⟩
/-- `Instr.testRI` -- `TEST r/m, imm32`. -/
def testRI : Name := ⟨"Grass.ISA.X86.Target.Instr.testRI"⟩
/-- `Instr.syscall`. -/
def syscall : Name := ⟨"Grass.ISA.X86.Target.Instr.syscall"⟩
/-- `Instr.ud2`. -/
def ud2 : Name := ⟨"Grass.ISA.X86.Target.Instr.ud2"⟩
/-- `Instr.hlt`. -/
def hlt : Name := ⟨"Grass.ISA.X86.Target.Instr.hlt"⟩

/-- `condHolds` -- the Jcc/SETcc/CMOVcc condition-code table. -/
def condHolds : Name := ⟨"Grass.ISA.X86.Target.condHolds"⟩
/-- `addSubFlags` -- the ADD/SUB/CMP CF/OF definitions. -/
def addSubFlags : Name := ⟨"Grass.ISA.X86.Target.addSubFlags"⟩
/-- `regWrite` -- 32-bit writes zero-extend, 64-bit writes replace. -/
def regWrite : Name := ⟨"Grass.ISA.X86.Target.regWrite"⟩
/-- `execInstr`'s use of the following instruction's address as the base of
every relative branch target. -/
def ripRelativeNextInstruction : Name :=
  ⟨"Grass.ISA.X86.Target.execInstr.ripRelativeNextInstruction"⟩
/-- `execInstr`'s `.syscall` case, and the register set SYSCALL clobbers that
its `NativeReturn.clobbers` delegate must include. -/
def syscallClobbers : Name := ⟨"Grass.ISA.X86.Target.execInstr.syscallClobbers"⟩

end Subject

/-- Build a checked dual citation for a seam subject. Mirrors
`Grass.ISA.X86.Rules.dual` (private to `Profile.lean`); duplicated rather than
exported so each file keeps its own obligations local to its own subjects. -/
private def dc (subject : Name) (intel amd : Citation)
    (hip : intel.publisher = Vendor.intel.publisher := by decide)
    (hap : amd.publisher = Vendor.amd.publisher := by decide)
    (hic : intel.covers subject = true := by decide)
    (hac : amd.covers subject = true := by decide)
    (hiw : intel.WellFormed := by decide)
    (haw : amd.WellFormed := by decide) : DualCitation subject :=
  { intel := intel, amd := amd
    intelPublisher := hip, amdPublisher := hap
    intelCovers := hic, amdCovers := hac
    intelWellFormed := hiw, amdWellFormed := haw }

/-! ## `MOV`, register/immediate forms -/

/-- `docs/REFERENCES.md`'s inspected MOV pages, shared by all three MOV
constructors below (one instruction-reference entry covers every addressing
form). -/
def movRRRule : CommonRule :=
  { subject := Subject.movRR
    statement :=
      "MOV r/m, r copies the source register into the destination register. " ++
      "Its write-back width rule (32-bit zero-extends, 64-bit replaces) is " ++
      "`Subject.regWrite`'s claim, not restated here."
    basis := .assertedPendingConfirmation
    citation := dc Subject.movRR
      (cite .intel "Vol. 2A-2D" "MOV" "Move" [Subject.movRR]
        "Printed pages 4-28-4-30 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.")
      (cite .amd Volume.amdInstructions "MOV" "Move" [Subject.movRR]
        "Printed pages 240-242 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.") }

/-- Same MOV entry as `movRRRule`, immediate-to-register form. -/
def movRI32Rule : CommonRule :=
  { subject := Subject.movRI32
    statement :=
      "MOV r32, imm32 writes the 32-bit immediate into the named register " ++
      "and zero-extends to 64 bits, per `Subject.regWrite`."
    basis := .assertedPendingConfirmation
    citation := dc Subject.movRI32
      (cite .intel "Vol. 2A-2D" "MOV" "Move" [Subject.movRI32]
        "Printed pages 4-28-4-30 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.")
      (cite .amd Volume.amdInstructions "MOV" "Move" [Subject.movRI32]
        "Printed pages 240-242 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.") }

/-- Same MOV entry as `movRRRule`, 64-bit immediate form. -/
def movRI64Rule : CommonRule :=
  { subject := Subject.movRI64
    statement :=
      "MOV r64, imm64 replaces the named 64-bit register with the immediate."
    basis := .assertedPendingConfirmation
    citation := dc Subject.movRI64
      (cite .intel "Vol. 2A-2D" "MOV" "Move" [Subject.movRI64]
        "Printed pages 4-28-4-30 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.")
      (cite .amd Volume.amdInstructions "MOV" "Move" [Subject.movRI64]
        "Printed pages 240-242 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.") }

/-! ## `TEST` -/

/-- `docs/REFERENCES.md`'s inspected TEST pages. -/
def testRRRule : CommonRule :=
  { subject := Subject.testRR
    statement :=
      "TEST r/m, r computes the bitwise AND of its operands, sets flags from " ++
      "the result without writing it back, and always clears CF and OF; " ++
      "`execInstr`'s `.testRR` case reuses `aluApply .and_` for exactly this " ++
      "reason and discards the computed value. This profile carries no AF/PF " ++
      "field, so TEST's undefined-AF behaviour is outside this rule's scope " ++
      "rather than modeled incorrectly."
    basis := .assertedPendingConfirmation
    citation := dc Subject.testRR
      (cite .intel "Vol. 2A-2D" "TEST" "Logical Compare" [Subject.testRR]
        "Printed pages 4-720-4-721 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.")
      (cite .amd Volume.amdInstructions "TEST" "Logical Compare" [Subject.testRR]
        "Printed pages 360-361 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.") }

/-- Same TEST entry as `testRRRule`, immediate form. -/
def testRIRule : CommonRule :=
  { subject := Subject.testRI
    statement :=
      "TEST r/m, imm32 is the same bitwise-AND-and-discard operation as " ++
      "`testRR` against an immediate instead of a register."
    basis := .assertedPendingConfirmation
    citation := dc Subject.testRI
      (cite .intel "Vol. 2A-2D" "TEST" "Logical Compare" [Subject.testRI]
        "Printed pages 4-720-4-721 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.")
      (cite .amd Volume.amdInstructions "TEST" "Logical Compare" [Subject.testRI]
        "Printed pages 360-361 inspected per docs/REFERENCES.md's register-semantics anchors; Citation.confirmed has not been set for this subject.") }

/-! ## `SYSCALL`, `UD2`, `HLT`

None of these three has an inspected page recorded in `docs/REFERENCES.md`.
Their section identifiers below name the instruction-reference entry itself
(the mnemonic, which is how both manuals key these one-page entries) rather
than a numbered subsection, and `confirmed` stays `none`: this is working
knowledge of where the entries live, not a followed anchor. -/

/-- SYSCALL transfers control without pushing a return address; `execInstr`
models it as an external call for exactly that reason. -/
def syscallRule : CommonRule :=
  { subject := Subject.syscall
    statement :=
      "SYSCALL (opcode `0F 05`) transfers control to the address the " ++
      "operating system configured, without pushing a return address on the " ++
      "stack. `Instr.syscall`/`execInstr`'s `.syscall` case models it as an " ++
      "external call rather than an internal step for exactly that reason."
    basis := .assertedPendingConfirmation
    citation := dc Subject.syscall
      (cite .intel "Vol. 2B" "SYSCALL" "SYSCALL-Fast System Call" [Subject.syscall]
        "Unconfirmed; from working knowledge of the instruction-reference entry's location, not yet located against revision 092 by this corpus.")
      (cite .amd Volume.amdInstructions "SYSCALL" "SYSCALL" [Subject.syscall]
        "Unconfirmed; from working knowledge of the instruction-reference entry's location, not yet located against APM revision 4.10 by this corpus.") }

/-- UD2 always raises an invalid-opcode fault. -/
def ud2Rule : CommonRule :=
  { subject := Subject.ud2
    statement :=
      "UD2 (opcode `0F 0B`) is defined to always raise an invalid-opcode " ++
      "fault; `execInstr`'s `.ud2` case models it as " ++
      "`.fault .explicitUndefined` rather than a no-op or an internal step " ++
      "for that reason."
    basis := .assertedPendingConfirmation
    citation := dc Subject.ud2
      (cite .intel "Vol. 2B" "UD2" "UD2-Undefined Instruction" [Subject.ud2]
        "Unconfirmed; from working knowledge of the instruction-reference entry's location, not yet located against revision 092 by this corpus.")
      (cite .amd Volume.amdInstructions "UD2" "UD2" [Subject.ud2]
        "Unconfirmed; from working knowledge of the instruction-reference entry's location, not yet located against APM revision 4.10 by this corpus.") }

/-- HLT stops execution until an enabling condition occurs. -/
def hltRule : CommonRule :=
  { subject := Subject.hlt
    statement :=
      "HLT (opcode `F4`) stops instruction execution until an enabling " ++
      "condition occurs; `execInstr`'s `.hlt` case models it as `.halted` " ++
      "rather than an internal step or a fault."
    basis := .assertedPendingConfirmation
    citation := dc Subject.hlt
      (cite .intel "Vol. 2B" "HLT" "HLT-Halt" [Subject.hlt]
        "Unconfirmed; from working knowledge of the instruction-reference entry's location, not yet located against revision 092 by this corpus.")
      (cite .amd Volume.amdInstructions "HLT" "HLT" [Subject.hlt]
        "Unconfirmed; from working knowledge of the instruction-reference entry's location, not yet located against APM revision 4.10 by this corpus.") }

/-! ## Execution facts that are not about one instruction -/

/-- The Jcc/SETcc/CMOVcc condition-code table. -/
def condHoldsRule : CommonRule :=
  { subject := Subject.condHolds
    statement :=
      "Each of the sixteen condition-code mnemonics Jcc/SETcc/CMOVcc share " ++
      "evaluates to a fixed boolean function of CF/ZF/SF/OF given by the " ++
      "architectural condition-code table; `Cond` enumerates exactly those " ++
      "sixteen codes in their encoding order and `condHolds` evaluates each " ++
      "against this profile's four modeled flags. Parity (P/NP) is " ++
      "unconditionally false/true here because this profile carries no PF " ++
      "field, not because the architecture defines it that way."
    basis := .assertedPendingConfirmation
    citation := dc Subject.condHolds
      (cite .intel Volume.intelBasic "3.4.3" "EFLAGS Register" [Subject.condHolds]
        "Unconfirmed. Table 3-1 in this section tabulates the sixteen condition-code mnemonics against CF/ZF/SF/OF/PF; find the table captioned for jcc/setcc/cmovcc condition codes and check each row against `Cond.code`/`condHolds`."
        (table := some "Table 3-1"))
      (cite .amd Volume.amdInstructions "Condition codes" "Condition codes" [Subject.condHolds]
        "Unconfirmed. AMD Vol. 3's instruction-encoding chapter documents the same sixteen condition codes; find that table and check each row against `Cond.code`/`condHolds`.") }

/-- ADD/SUB/CMP's CF/OF definitions, shared by `aluApply`'s `.add`/`.sub`/`.cmp`
cases via `addSubFlags`. -/
def addSubFlagsRule : CommonRule :=
  { subject := Subject.addSubFlags
    statement :=
      "For an addition (or a subtraction restated as addition of the " ++
      "negation, per SUB/CMP's own definition), CF is the unsigned " ++
      "carry/borrow out of the operand width and OF is set exactly when the " ++
      "two operands share a sign and the result's sign differs from theirs " ++
      "-- the signed-overflow condition `addSubFlags` computes for ADD, SUB " ++
      "and CMP alike."
    basis := .assertedPendingConfirmation
    citation := dc Subject.addSubFlags
      (cite .intel Volume.intelBasic "3.4.3" "EFLAGS Register" [Subject.addSubFlags]
        "Unconfirmed. Section 3.4.3 defines CF and OF in general terms; the already partly anchored per-instruction ADD/SUB/CMP pages (docs/REFERENCES.md) restate them for those specific operations.")
      (cite .amd Volume.amdApplication "3.1.4" "Status Flags" [Subject.addSubFlags]
        "Unconfirmed. Not yet located against APM revision 4.10 by this corpus.") }

/-- 32-bit register writes zero-extend to 64 bits; 64-bit writes replace the
whole register. The same fact `Grass.ISA.X86.Rules.registerWriteExtension`
already carries for the legacy decoder's `writeBack`, restated here for the
seam's own `regWrite`. -/
def regWriteRule : CommonRule :=
  { subject := Subject.regWrite
    statement :=
      "Writing an sz-wide value to a general-purpose register replaces the " ++
      "full 64-bit register when sz = w64; when sz = w32 it replaces only " ++
      "bits 31:0 and clears bits 63:32."
    basis := .assertedPendingConfirmation
    citation := dc Subject.regWrite
      (cite .intel Volume.intelBasic "3.4.1.1" "General-Purpose Registers in 64-Bit Mode"
        [Subject.regWrite]
        "Same passage `Grass.ISA.X86.Rules.registerWriteExtension` already confirmed for the legacy decoder's writeBack rule (\"32-bit operands generate a 32-bit result, zero-extended to a 64-bit result\"); reused here for the seam's regWrite, which restates the same 32-bit zero-extension over a different declaration."
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "2.5.1" "64-Bit Operand Size" [Subject.regWrite]
        "Unconfirmed, and a different anchor from `Grass.ISA.X86.Rules.registerWriteExtension`'s AMD citation (Vol. 1 section 3.1.2, which is confirmed): this is the instruction-volume restatement of the same rule, and nobody has opened it in this corpus yet.") }

/-- RIP-relative addressing is measured from the address of the *next*
instruction. No single declaration owns "next instruction" -- every
`execInstr` case that branches computes `next.rip = s.rip + len` once and
passes it to `effAddr` -- so this subject anchors to `execInstr` with one
discriminator, matching `Grass/ISA/X86/Profile.lean`'s
`decodeMem.ripRelative` convention. -/
def ripRelativeNextInstructionRule : CommonRule :=
  { subject := Subject.ripRelativeNextInstruction
    statement :=
      "A RIP-relative effective address is the signed 32-bit displacement " ++
      "added to the address of the instruction following the one that uses " ++
      "it, not the address of the instruction itself. `execInstr` computes " ++
      "every branch target (`callRel32`, `jmpRel32`, `jmpRel8`, `jccRel32`, " ++
      "`jccRel8`) as `effAddr next.rip rel`, where `next.rip = s.rip + len` " ++
      "is already the following instruction's address; this rule is what " ++
      "licenses using `next.rip` rather than `s.rip` there."
    basis := .assertedPendingConfirmation
    citation := dc Subject.ripRelativeNextInstruction
      (cite .intel Volume.intelInstructionFormat "2.2.1.6" "RIP-Relative Addressing"
        [Subject.ripRelativeNextInstruction]
        "Same passage `Grass.ISA.X86.Rules.ripRelativeForm` already confirmed (\"by adding displacement to the 64-bit RIP of the next instruction\"). Reused here for the seam's own next-instruction-relative branch targets, a different declaration from the legacy decoder's `decodeMem.ripRelative`."
        (confirmed := some intelAnchorCheckDate))
      (cite .amd Volume.amdInstructions "1.7.1" "RIP-Relative Addressing"
        [Subject.ripRelativeNextInstruction]
        "Same passage `Grass.ISA.X86.Rules.ripRelativeForm` already confirmed: its locator names \"section 1.7.1/Table 1-16\" within Vol. 3 rev. 3.38 pp. 24-26 for the next-instruction-RIP claim. Reused here for the seam's branch-target computation."
        (confirmed := some amdAnchorCheckDate)
        (page := some 24)) }

/-- SYSCALL clobbers rcx (loaded with the return RIP) and r11 (loaded with
RFLAGS), beyond whatever the target's own calling convention documents.
`execInstr`'s `.syscall` case does not hardcode this -- it delegates the
clobber set to the platform's `NativeReturn.clobbers` -- so this rule is the
architectural reason a platform binding must include rcx and r11 there,
not a claim about code in this file. -/
def syscallClobbersRule : CommonRule :=
  { subject := Subject.syscallClobbers
    statement :=
      "SYSCALL clobbers rcx and r11 in addition to any register the " ++
      "target's own calling convention documents."
    basis := .assertedPendingConfirmation
    citation := dc Subject.syscallClobbers
      (cite .intel "Vol. 2B" "SYSCALL" "SYSCALL-Fast System Call" [Subject.syscallClobbers]
        "Unconfirmed; from working knowledge, not yet located against revision 092 by this corpus. Find the SYSCALL instruction reference entry's \"Operation\" section, which loads RCX and R11 before transferring control.")
      (cite .amd Volume.amdInstructions "SYSCALL" "SYSCALL" [Subject.syscallClobbers]
        "Unconfirmed; from working knowledge, not yet located against APM revision 4.10 by this corpus.") }

/-! ## The ledger -/

/-- Every cited rule. Thirteen entries: eight `Instr` constructors and five
non-per-instruction execution facts. See this module's header for why the
other 25 constructors are not here. -/
def seamCommon : List CommonRule :=
  [movRRRule, movRI32Rule, movRI64Rule, testRRRule, testRIRule,
   syscallRule, ud2Rule, hltRule,
   condHoldsRule, addSubFlagsRule, regWriteRule,
   ripRelativeNextInstructionRule, syscallClobbersRule]

/-- The seam ISA's trust ledger. No refinements or exclusions yet: nothing
cited below is vendor-specific, and nothing has been reviewed and excluded
from the model. -/
def seamLedger : Ledger :=
  { profile := ⟨"Grass.ISA.X86.Target"⟩
    common := seamCommon
    refinements := []
    exclusions := [] }

/-- The ledger does not contradict itself: no subject is claimed twice, and
nothing is both modeled and excluded. See `Ledger.Coherent`. -/
theorem seamLedger_coherent : seamLedger.Coherent := by decide

/-!
### Coverage is not proved here

As `Grass/ISA/X86/Profile.lean` explains for `commonProfileLedger`, a coverage
theorem stated in this file could only ever compare `seamLedger` against a
hand-written list built from the same declarations, which is circular by
construction. The actual coverage obligation -- every constructor of `Instr`
and every top-level declaration of `Grass.ISA.X86.Target` is cited, waived, or
owed -- comes from the Lean environment in
`Tests/ISA/X86/SeamLedgerAudit.lean`, which this file cannot shrink.
-/

/-! ## Pending rows: the concurrent memory-operand family

See this module's header. Deliberately **not** a `List CommonRule`: a
`DualCitation` demands `covers subject = true` on a real `Citation.subjects`
list naming a real declaration. The worklist itself does not establish that a
name resolves to one. `PendingRow` is unaudited prose -- `Tests/ISA/X86/SeamLedgerAudit.lean`
does not read this list, so adding or removing an entry here changes no gate.
It exists so the integrator adding these constructors has the citation
research already done. -/

/-- A future `Instr` constructor's intended citation, recorded before the
constructor exists. -/
structure PendingRow where
  /-- The constructor's name, once it lands. Not required to resolve to a
  real declaration -- that is the point. -/
  subject : Name
  /-- What the instruction is, in one line. -/
  describes : String
  /-- Where its citation should come from, and which already-cited seam
  subject (if any) it shares a fact with. -/
  intendedCitation : String

/-- Intended citations for the eleven memory-operand constructors
`Grass/ISA/X86/Target/Encode.lean` and `Grass/ISA/X86/Target.lean` are being
extended with concurrently. Promote an entry into `seamCommon` (as a real
`CommonRule` with a `Subject.*` constant matching the landed constructor name)
once its constructor exists; `Tests/ISA/X86/SeamLedgerAudit.lean`'s Gate B
will otherwise report it `owed` the moment it lands, which is the correct
default until someone does. -/
def pendingMemoryOperandFamily : List PendingRow :=
  [ { subject := ⟨"Grass.ISA.X86.Target.Instr.movRM"⟩
      describes := "MOV r, r/m -- load form: register or [base+disp32] source."
      intendedCitation :=
        "Same MOV entry as Subject.movRR (Intel Vol. 2A-2D pp. 4-28-4-30 / " ++
        "AMD Vol. 3 pp. 240-242)." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.movMR"⟩
      describes := "MOV r/m, r -- store form: register or [base+disp32] destination."
      intendedCitation := "Same MOV entry as Subject.movRR." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.movMI32"⟩
      describes := "MOV r/m32, imm32 -- store-immediate form."
      intendedCitation := "Same MOV entry as Subject.movRR." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.movzxRM8"⟩
      describes := "MOVZX r, r/m8 -- zero-extending byte load from memory."
      intendedCitation :=
        "MOVZX has no citation anywhere in this corpus yet (`movzxRR` is " ++
        "itself owed below); needs its own Intel/AMD MOVZX page, not " ++
        "located in docs/REFERENCES.md." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.movMR8"⟩
      describes := "MOV r/m8, r8 -- byte store."
      intendedCitation :=
        "Same MOV entry as Subject.movRR for the store itself; the byte-" ++
        "register operand it names additionally touches " ++
        "`Grass.ISA.X86.Rules.byteRegisterRexInteraction` (already confirmed) " ++
        "if this form allows the legacy AH/CH/DH/BH encodings." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.leaRM"⟩
      describes := "LEA r, [base+disp32] -- load effective address, no memory access."
      intendedCitation :=
        "Intel LEA 3-547-3-548 inspected in docs/REFERENCES.md; still needs " ++
        "formal Intel/AMD subject enrollment." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.leaRip"⟩
      describes := "LEA r, [rip+disp32]."
      intendedCitation :=
        "LEA's own page (see leaRM above) plus " ++
        "Subject.ripRelativeNextInstruction for the RIP-relative half." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.movRMrip"⟩
      describes := "MOV r, [rip+disp32] -- RIP-relative load."
      intendedCitation :=
        "Same MOV entry as Subject.movRR plus " ++
        "Subject.ripRelativeNextInstruction." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.callRip"⟩
      describes := "CALL [rip+disp32] -- indirect call through a RIP-relative operand."
      intendedCitation :=
        "Intel CALL 3-121-3-130 inspected in docs/REFERENCES.md; still needs " ++
        "formal Intel/AMD CALL subject enrollment, plus " ++
        "Subject.ripRelativeNextInstruction for the addressing half." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.cmpMI32"⟩
      describes := "CMP r/m32, imm32."
      intendedCitation :=
        "CMP's printed pages (Intel 3-161-3-162 / AMD 162-164) are already " ++
        "inspected per docs/REFERENCES.md and can be cited directly, the " ++
        "same way movRRRule/testRRRule are, once this constructor exists." },
    { subject := ⟨"Grass.ISA.X86.Target.Instr.aluRM"⟩
      describes := "<op> r, r/m -- RM-form ALU, six mnemonics sharing one opcode-dispatch shape."
      intendedCitation :=
        "Same partial coverage problem as the existing aluRR/aluRI: ADD, " ++
        "SUB, XOR and CMP have inspected pages, OR and AND do not. Owed on " ++
        "arrival for the same reason, not a citation gap specific to the " ++
        "memory form." } ]

end Grass.ISA.X86.Target
