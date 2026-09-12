import Lean.Elab.Command
import Grass.ISA.X86.Target
import Grass.ISA.X86.Target.Ledger

/-!
# Seam ledger coverage gate

`docs/DECISIONS.md` 21 requires every modeled instruction/API behaviour to
carry a citation, and `docs/FOUNDATION.md` law 1 says the same: "No semantic
invention: ISA/API behavior requires an authoritative citation." Commit
`6a7ea03a` deleted the mechanized enforcement of that for the legacy decoder
(`Tests/ISA/X86/LedgerAudit.lean`, 1,692 lines, auditing
`Grass.ISA.X86.Profile.commonProfileLedger`) and its CI step. It never audited
the seam instruction set at all: `Grass/ISA/X86/Target/Encode.lean`'s `Instr`
and `Grass/ISA/X86/Target.lean`'s `execInstr` did not exist in that ledger's
scope, so they had no mechanized citation gate either before or after the
deletion. This file is that gate for the seam, following the deleted file's
shape.

## What this audits, and what it does not

Two enumerations, both narrower than the deleted file's whole-tree walk
because the seam is one small, freshly-written instruction set rather than
the seven-module legacy decoder tree:

- every constructor of `Grass.ISA.X86.Target.Instr` (`Grass/ISA/X86/Target/Encode.lean`),
  found by reflection on the inductive declaration rather than a hand-written
  list, so a new constructor cannot be invisible to this gate the way a new
  module was invisible to the deleted file before its `notModelling`/disk-walk
  fix;
- every top-level declaration of the module `Grass.ISA.X86.Target`, i.e.
  literally written in `Grass/ISA/X86/Target.lean` (`execInstr`, `step`,
  `initial`, and their helpers -- `Grass.ISA.X86.isa` lives in the same file
  and is therefore in scope too, despite its different namespace).

`Grass/ISA/X86/Target/Encode.lean`'s *other* declarations (`Sz`, `AluOp`,
`Cond`, `encode`, `decode`, and the round-trip proof machinery) are
deliberately out of scope: they are a different module
(`Grass.ISA.X86.Target.Encode`), and the round-trip theorem
(`Instr.decode_encode`) is `Grass/ISA/X86/Target/Encode.lean`'s own proof
obligation, not a citation obligation -- reusing `Grass.ISA.X86.Gpr`,
`Rex`/`ModRm`/`Sib` and `encodeMem`/`decodeMem` is exactly what
`Grass/ISA/X86/Target/Encode.lean`'s own header says it does, and those are
already citation-audited (or owed) under `Grass.ISA.X86.Rules` in the deleted
`LedgerAudit.lean`'s scope, now unenforced only for the reason this whole
finding names -- the CI step, not the citations themselves, was removed. This
file does not restore that broader gate; it adds the one this repository never
had.

## Three buckets, same discipline as the deleted file

A declaration accounted for by `Grass.ISA.X86.Target.seamLedger` (a real
citation), explicitly `notBehaviour` (reviewed, carries no external claim), or
explicitly `owed` (a real citation debt, printed every run, may only shrink)
passes. Anything else fails the build. The three buckets must partition the
audited set -- disjoint, and summing to the modeled count -- for the same
reason the deleted file's docstring gives: a summary line that reads as a
partition and is not one is worse than an honest count, because a reviewer
scanning "N owed, M waived" has no way to notice `decodeMem`-style double
counting without recomputing it by hand.

## Verifying the gate is not vacuous

Two checks the deleted file made falsifiable, reproduced here the same way:

1. **A modeled declaration outside all three buckets fails the build.**
   Checked by temporarily deleting `Grass.ISA.X86.Target.regRead` from
   `notBehaviour` below, running `lake env lean Tests/ISA/X86/SeamLedgerAudit.lean`,
   and confirming it failed with exactly the "models external behaviour with no
   citation" error naming `regRead`, then restoring the entry. This is the
   same failure Gate B below produces for a genuinely new uncited declaration
   in `Grass/ISA/X86/Target.lean`; that file could not be edited to run the
   equivalent check directly; it is owned by a concurrently-running agent
   adding the memory-operand instruction family, and this repository's rules
   forbid editing it even temporarily. Removing bucket membership and adding an
   uncited declaration are the same perturbation as far as Gate B's predicate
   is concerned -- `!(accountedBy ...) && !(notBehaviour.contains d) && !(owed.contains d)`
   does not distinguish "never was in a bucket" from "removed from a bucket" --
   so this is an equivalent falsification, not an approximation of one.
2. **The three buckets are checked to partition, not assumed to.** Checked by
   temporarily adding `Grass.ISA.X86.Target.Instr.push` (already `owed`) to
   `notBehaviour` as well, running the same command, and confirming it failed
   with the "is in both owed and notBehaviour" error, then removing it again.
-/

namespace Grass.Tests.ISA.X86.SeamLedgerAudit

open Lean Elab Command Grass.ISA.X86.Target

/-- The module literally written as `Grass/ISA/X86/Target.lean`. Shares this
name with the `Grass.ISA.X86.Target` *namespace* most of that file's
declarations sit in, but a Lean module is the file, not the namespace: `def
isa` sits in `namespace Grass.ISA.X86` at the bottom of the same file and is
therefore still found by filtering on this module, under the name
`Grass.ISA.X86.isa`. -/
def targetModule : Name := `Grass.ISA.X86.Target

/-- `Grass.ISA.X86.Target.Instr`, audited by its constructors rather than as a
single declaration. -/
def instrType : Name := `Grass.ISA.X86.Target.Instr

/-- Compiler-generated names that are not authored declarations. Copied from
`Tools/AxiomAudit.lean`'s `generatedSuffixes` companion in the deleted
`Tests/ISA/X86/LedgerAudit.lean`, for the same reason: `Sz.default`,
`Instr.rec` and their siblings are not declarations an author wrote or a
citation obligation. -/
def generatedSuffixes : List Name :=
  [`rec, `recOn, `casesOn, `below, `brecOn, `ibelow, `binductionOn, `elim,
   `noConfusion, `noConfusionType, `ctorIdx, `toCtorIdx, `ctorElim,
   `ctorElimType, `ofNat, `injEq, `mk,
   `sizeOf_spec, `decEq, `repr, `default, `eq_def, `induct, `fun_cases]

/-- The name a declaration is written under, with any `private` mangling
removed. `Grass.ISA.X86.Target.sectionByte`/`sectionRegions` are both
`private`, and the same defect the deleted file records for the legacy
decoder's `takeByte`/`takeDisp`/etc. applies here: without this, `isAudited`
would silently skip them, and each is exactly the kind of declaration this
ledger exists to account for. -/
def userFacing (n : Name) : Name := (privateToUserName? n).getD n

/-- Whether a name was produced by elaboration rather than authored. Same
heuristic as the deleted `Tests/ISA/X86/LedgerAudit.lean`'s `isGenerated`: a
compiler helper hangs off something. -/
def isGenerated (n : Name) : MetaM Bool := do
  if n.hasMacroScopes then return true
  match n with
  | .str parent last =>
      let env ← getEnv
      let parentIsConstant := (env.find? parent).isSome
      if n.components.any fun c =>
          ["match_", "eq_", "proof_", "sunfold", "induct_"].any (c.toString.startsWith ·)
        then return true
      if last.startsWith "_" || generatedSuffixes.any (·.toString == last) then
        return parentIsConstant || (← Meta.isInstance parent)
      return false
  | _ => return false

/--
Declarations reviewed and found to carry no claim about a processor.

A permanent claim, one line of reasoning each -- see
`Grass/ISA/X86/Target/Ledger.lean`'s header for why each is not itself an
architecture fact.
-/
def notBehaviour : List Name :=
  [ -- Pure projections of the already-loaded `Sectioned` program; no claim
    -- about a loader beyond reading the bytes/permissions it already carries.
    `Grass.ISA.X86.Target.sectionByte,
    `Grass.ISA.X86.Target.sectionRegions,
    -- Grass's own choice of how to map a loaded program and platform context
    -- into `State` (stack/argument-block permissions, register placement);
    -- not a vendor claim, since no manual specifies Grass's internal `State`.
    `Grass.ISA.X86.Target.initial,
    -- The read half of `regWrite`'s already-cited zero-extension rule: masking
    -- to the low 32 bits on a `w32` read is the dual of clearing them on a
    -- `w32` write, not an independent architectural claim.
    `Grass.ISA.X86.Target.regRead,
    -- Derived numeric constants from a chosen operand width (32 or 64 bits):
    -- the all-ones mask, the sign-bit mask, and the byte count are arithmetic
    -- consequences of `Sz`, not separate vendor facts.
    `Grass.ISA.X86.Target.maskFor,
    `Grass.ISA.X86.Target.signBitFor,
    `Grass.ISA.X86.Target.byteCount,
    -- Compose already-classified facts (byte order is `owed` below; width is
    -- `notBehaviour` above) with `State`'s own `readBytes`/`writeBytes`; add
    -- no new fact of their own.
    `Grass.ISA.X86.Target.readMem,
    `Grass.ISA.X86.Target.writeMem,
    -- Dispatches to `addSubFlags` (cited) or `logicFlags` (owed) per
    -- operation and computes the result value by ordinary modular arithmetic
    -- or bitwise operation; the dispatch itself asserts nothing new.
    `Grass.ISA.X86.Target.aluApply,
    -- Fetch/decode/execute orchestration and fault classification over
    -- `State`'s own memory-region model (out of this file's scope) and
    -- `decode` (audited under `Grass.ISA.X86.Target.Encode`, a different
    -- module); no new architecture fact.
    `Grass.ISA.X86.Target.step,
    -- Structure literal assembling the already-classified `Instr`/`encode`/
    -- `decode`/`State`/`initial`/`step` into `Grass.Target.ISA`; asserts
    -- nothing beyond its fields.
    `Grass.ISA.X86.isa ]

/-- The number of entries `notBehaviour` was last reviewed at. Ratcheted
separately from and more strongly than `owed`, for the reason the deleted
`Tests/ISA/X86/LedgerAudit.lean` gives: reclassifying a declaration out of
`owed` into this permanent-waiver list discharges debt without a citation. -/
def notBehaviourBaseline : Nat := 12

/--
Declarations that genuinely model external behaviour and have no citation yet.

Debt, not a waiver. Printed on every run; may only shrink. See
`Grass/ISA/X86/Target/Ledger.lean`'s header for why each of these specifically
lacks a citation rather than being cited outright.
-/
def owed : List Name :=
  [ -- Native reply ordering and the post-effect indirect return are explicit
    -- hosted execution obligations, not citation-free state plumbing.
    `Grass.ISA.X86.Target.applyNativeReturn,
    `Grass.ISA.X86.Target.resumeIndirect,
    -- The memory family now uses modulo-64 effective-address arithmetic.
    -- This architectural rule is no longer classified as branch-only plumbing.
    `Grass.ISA.X86.Target.effAddr,
    -- Bounded disp32 memory forms. Primary instruction entries were inspected;
    -- formal dual-vendor subject enrollment remains explicit debt.
    `Grass.ISA.X86.Target.Instr.movRM,
    `Grass.ISA.X86.Target.Instr.movMI32,
    `Grass.ISA.X86.Target.Instr.leaRM,
    `Grass.ISA.X86.Target.Instr.leaRip,
    `Grass.ISA.X86.Target.Instr.callRip,
    -- Little-endian byte packing/unpacking for memory operands. x86-64's
    -- byte order is a real architectural fact with no anchor recorded in
    -- docs/REFERENCES.md or docs/AMD_SOURCE_MIGRATION.md for this
    -- declaration; `Grass.ISA.X86.le32`/`le64` cite it for the *encoding*
    -- byte stream, but memory read/write order is a separate claim.
    `Grass.ISA.X86.Target.leToUInt64,
    `Grass.ISA.X86.Target.toLE,
    -- AND/OR/XOR/TEST's flag-clearing behaviour (CF/OF always cleared,
    -- ZF/SF from the result). No anchor located for this declaration.
    `Grass.ISA.X86.Target.logicFlags,
    -- MOVSX's sign-extension-from-width computation. No anchor located.
    `Grass.ISA.X86.Target.signExtendFrom,
    -- The imm32-sign-extended-to-operand-size rule behind `81 /digit id`
    -- and `F7 /0 id` (found 2026-09-10 by SeamNativeCorpus's cross-check:
    -- the seam zero-extended). No anchor recorded for this declaration.
    `Grass.ISA.X86.Target.immSx,
    -- POP's read-then-increment order and PUSH/POP's shared stack-pointer
    -- update. No anchor located for either half.
    `Grass.ISA.X86.Target.popValue,
    -- 25 of `Instr`'s 33 constructors: no Intel/AMD anchor is recorded in
    -- docs/REFERENCES.md or docs/AMD_SOURCE_MIGRATION.md for any of these.
    -- `aluRR`/`aluRI` are the sharpest case: four of the six ALU mnemonics
    -- each covers (ADD, SUB, XOR, CMP) have inspected pages, OR and AND do
    -- not, so citing the constructor as fully covered would overstate what
    -- has been checked.
    `Grass.ISA.X86.Target.Instr.movzxRR,
    `Grass.ISA.X86.Target.Instr.movsxRR,
    `Grass.ISA.X86.Target.Instr.aluRR,
    `Grass.ISA.X86.Target.Instr.aluRI,
    `Grass.ISA.X86.Target.Instr.shiftImm,
    `Grass.ISA.X86.Target.Instr.imul2,
    `Grass.ISA.X86.Target.Instr.inc,
    `Grass.ISA.X86.Target.Instr.dec,
    `Grass.ISA.X86.Target.Instr.push,
    `Grass.ISA.X86.Target.Instr.pop,
    `Grass.ISA.X86.Target.Instr.callRel32,
    `Grass.ISA.X86.Target.Instr.ret,
    `Grass.ISA.X86.Target.Instr.jmpRel32,
    `Grass.ISA.X86.Target.Instr.jmpRel8,
    `Grass.ISA.X86.Target.Instr.jccRel32,
    `Grass.ISA.X86.Target.Instr.jccRel8,
    `Grass.ISA.X86.Target.Instr.nop,
    `Grass.ISA.X86.Target.Instr.cdq,
    `Grass.ISA.X86.Target.Instr.cqo,
    `Grass.ISA.X86.Target.Instr.div,
    `Grass.ISA.X86.Target.Instr.idiv,
    `Grass.ISA.X86.Target.Instr.mul,
    `Grass.ISA.X86.Target.Instr.setcc,
    `Grass.ISA.X86.Target.Instr.cmovcc,
    `Grass.ISA.X86.Target.Instr.xchgRR ]

/-- The number of entries `owed` was last reviewed at. May only shrink; a
genuinely new modeled declaration that owes a citation raises this in the same
reviewed edit that adds it, per `docs/VALIDATION.md` §7's ratchet. -/
def owedBaseline : Nat := 39

/-- Every constructor of `Grass.ISA.X86.Target.Instr`. -/
def instrConstructors : MetaM (Array Name) := do
  let indVal ← getConstInfoInduct instrType
  return indVal.ctors.toArray

/-- Every top-level declaration literally written in `Grass/ISA/X86/Target.lean`
(module `targetModule`), filtered the same way the deleted
`Tests/ISA/X86/LedgerAudit.lean` filtered its whole-tree walk: no generated
names, no constructors/inductives/theorems (`Instr`'s own constructors are
audited separately by `instrConstructors`; `Grass.ISA.X86.Target.Instr` the
type is not itself a subject any more than `Bool` is), no `Prop`-valued
declarations, and no projection functions. -/
def targetModuleDeclarations : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some midx := env.getModuleIdxFor? n | continue
    let some mname := env.header.moduleNames[midx.toNat]? | continue
    unless mname == targetModule do continue
    if ← isGenerated n then continue
    if ci.isCtor || ci.isInductive || ci.isTheorem then continue
    if ← Meta.isProp ci.type then continue
    if ← isProjectionFn n then continue
    out := out.push (userFacing n)
  return out

/-- The full audited set: `Instr`'s constructors plus `Target.lean`'s own
declarations. -/
def modeledDeclarations : MetaM (Array Name) := do
  return (← instrConstructors) ++ (← targetModuleDeclarations)

/-- The declaration a subject is anchored to: its longest prefix that names a
real constant. Mirrors the deleted `Tests/ISA/X86/LedgerAudit.lean`'s
`subjectAnchor` exactly, for the same `decodeMem.ripRelative`-shaped
convention `Grass/ISA/X86/Target/Ledger.lean`'s
`execInstr.ripRelativeNextInstruction`/`execInstr.syscallClobbers` reuse. -/
def subjectAnchor (env : Environment) (s : Name) : Option Name := Id.run do
  let mut cur : Name := .anonymous
  let mut best : Option Name := none
  for c in s.components do
    cur := cur.append c
    if env.contains cur then best := some cur
  return best

/-- Gate A: a subject names a declaration, or a declaration plus exactly one
discriminator segment. -/
def anchorFault (env : Environment) (s : Name) : Option String :=
  match subjectAnchor env s with
  | none => some "names no declaration and has no declaration prefix"
  | some a =>
      if s.components.length - a.components.length > 1 then
        some s!"anchors only to {a}, which is more than one segment short"
      else none

/-- Gate B: some ledger subject anchors to this declaration. -/
def accountedBy (env : Environment) (subjects : List Name) (d : Name) : Bool :=
  subjects.any fun s => subjectAnchor env s == some d

end Grass.Tests.ISA.X86.SeamLedgerAudit

open Lean Elab Command Grass.ISA.X86.Target Grass.Tests.ISA.X86.SeamLedgerAudit in
run_cmd liftTermElabM do
  let env ← getEnv
  unless env.header.moduleNames.contains targetModule do
    logError m!"seam ledger audit expects to import {targetModule}, but it is not in the environment"
  let l := seamLedger
  let subjects :=
    (l.commonSubjects ++ l.refinedSubjects ++ l.excludedSubjects).map
      (fun n => n.text.toName)

  -- Gate A: subjects resolve.
  let anchorFaults := subjects.filterMap fun s =>
    (anchorFault env s).map (fun m => (s, m))
  for (s, m) in anchorFaults do
    logError m!"seam ledger subject {s} {m}"

  -- Gate B: every modeled declaration is accounted for.
  let modeled ← modeledDeclarations
  let unaccounted := modeled.filter fun d =>
    !(accountedBy env subjects d) && !(notBehaviour.contains d) && !(owed.contains d)
  for d in unaccounted do
    logError m!"{d} models external behaviour with no citation, and is in \
neither notBehaviour nor owed. Cite it in Grass/ISA/X86/Target/Ledger.lean, or \
add it to one of those lists under review."

  -- Stale entries in either list are their own defect.
  for d in notBehaviour do
    unless modeled.contains d do
      logError m!"notBehaviour lists {d}, which is not a modeled declaration"
  for d in owed do
    unless modeled.contains d do
      logError m!"owed lists {d}, which is not a modeled declaration"

  -- The three buckets must partition the audited set.
  for d in owed do
    if notBehaviour.contains d then
      logError m!"{d} is in both owed and notBehaviour; a declaration owes a \
citation or is reviewed as owing none, not both"
  for d in (owed ++ notBehaviour) do
    if accountedBy env subjects d then
      logError m!"{d} carries a citation but is also listed as owed or \
notBehaviour; remove it from that list"

  -- The debt may shrink and must not grow silently.
  if owed.length > owedBaseline then
    logError m!"owed has {owed.length} entries, above the reviewed baseline of \
{owedBaseline}. Debt may only shrink; if a genuinely new modeled declaration \
owes a citation, raise owedBaseline in the same reviewed edit."
  if notBehaviour.length > notBehaviourBaseline then
    logError m!"notBehaviour has {notBehaviour.length} entries, above the \
reviewed baseline of {notBehaviourBaseline}. This list is a permanent claim \
that a declaration carries no external behaviour, so it is ratcheted for the \
same reason owed is and more strongly: reclassifying a declaration out of owed \
discharges debt without a citation. Raise notBehaviourBaseline in the same \
reviewed edit if a genuinely new declaration belongs here."

  let cited := modeled.filter (accountedBy env subjects ·)
  logInfo m!"seam ledger audit: {modeled.size} modeled declarations ({(← instrConstructors).size} \
Instr constructors, {(← targetModuleDeclarations).size} Target.lean declarations) -- \
{cited.size} carry a citation, {owed.length} owed, \
{notBehaviour.length} reviewed as carrying no external behaviour. \
{subjects.length} ledger subjects, all anchoring to real declarations. \
{l.unconfirmedAnchors.length} of {l.citations.length} anchors are unconfirmed."
