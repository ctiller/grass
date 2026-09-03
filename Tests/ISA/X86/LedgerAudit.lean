import Lean.Elab.Command
import Grass.ISA.X86.Bytes
import Grass.ISA.X86.Profile

/-!
# Ledger coverage gate

`docs/DECISIONS.md` 21 requires every modeled instruction behaviour to carry a
citation. The ledger's own `Covers` theorem did not check that, and could not:
it compared a hand-written list against the ledger built from the same nine
constants, so `Rules.Subject.modeled = commonProfileLedger.commonSubjects` was
true by `rfl`. `commonProfileLedger_covers` was `∀ x ∈ L, x ∈ L`.

`Grass/ISA/X86/Ledger.lean` names the failure mode exactly — "deriving it would
let the ledger define its own obligation and always discharge it" — and then
writing the list by hand in the same namespace as the rules did the same thing
by a different route. `Tools/AxiomAudit.lean` had already learned this lesson
about import lists and walks the disk instead; this file does the same for
citations.

## The obligation comes from the environment

`modeledDeclarations` enumerates the declarations of the audited modules. The
ledger cannot shrink it. A new `def` in `Grass/ISA/X86/Addressing.lean` is
uncovered the moment it is written, and the author must cite it, waive it, or
record it as owed — all three under review.

## Three buckets, and why `owed` is not a waiver

A declaration is accounted for when a ledger subject anchors to it, or when it
appears in one of two explicit lists:

- `notBehaviour` — reviewed and found to carry no external behaviour. A
  convenience list, an internal predicate. This is a *permanent* claim and every
  entry states why.
- `owed` — genuinely needs a citation and does not have one yet. Not a waiver:
  it is printed on every run and must only shrink. `docs/VALIDATION.md` §7's
  ratchet discipline is the model — "Removing the resulting gate requires review
  explaining why the original finding can no longer recur."

Collapsing those two into one list is what would make this gate decorative. The
distinction is the difference between "this needs no citation" and "this needs a
citation and nobody has written it", and only the second is debt.

## What a subject may name

`Grass/ISA/X86/Profile.lean` names subjects like `decodeMem.ripRelative`, which
is not a declaration: several rules constrain `decodeMem` and they need distinct
names. That convention is fine and is now checkable. A subject must resolve to a
real declaration, optionally followed by **one** discriminator segment, so
`decodeMem.ripRelative` passes and `decodeMemm.ripRelative` — a typo — does not.

The discriminator itself is unverifiable in principle, which is exactly why the
coverage obligation runs over declarations rather than over subjects.
-/

namespace Grass.Tests.ISA.X86.LedgerAudit

open Lean Elab Command Grass.ISA.X86

/-- Modules whose declarations model external x86 behaviour and therefore owe a
citation under `docs/DECISIONS.md` 21.

The citation machinery itself is not modeled behaviour and is not audited: a
`Citation` record makes no claim about a processor. -/
def auditedModules : List Name :=
  [`Grass.ISA.X86.Register, `Grass.ISA.X86.Encoding,
   `Grass.ISA.X86.Addressing, `Grass.ISA.X86.Bytes]

/-- Compiler-generated names that are not authored declarations. -/
def generatedSuffixes : List Name :=
  [`rec, `recOn, `casesOn, `below, `brecOn, `ibelow, `binductionOn, `elim,
   `noConfusion, `noConfusionType, `ctorIdx, `toCtorIdx, `ctorElim,
   `ctorElimType, `ofNat, `injEq, `mk,
   `sizeOf_spec, `decEq, `repr, `default, `eq_def, `induct, `fun_cases]

/-- Whether a name was produced by elaboration rather than written. -/
def isGenerated (n : Name) : Bool :=
  n.isInternal
    || generatedSuffixes.any (·.isSuffixOf n)
    || n.components.any fun c =>
        let s := c.toString
        s.startsWith "match_" || s.startsWith "_" || s.startsWith "eq_"

/--
Declarations reviewed and found to carry no claim about a processor.

A permanent claim, one line of reasoning each. Anything here is asserting that a
reader could not be misled by its absence from the trust ledger.
-/
def notBehaviour : List Name :=
  [ -- Enumerations of Grass's own types. `Gpr.all` is a list of Grass
    -- constructors; the architectural fact is the numbering, which
    -- `Gpr.index` carries and which is cited.
    `Grass.ISA.X86.Gpr.all, `Grass.ISA.X86.Width.all,
    -- Grass-internal accessors over Grass's own representation. Each is a
    -- projection of a cited fact, not a separate claim about the machine.
    `Grass.ISA.X86.Gpr.ofIndex, `Grass.ISA.X86.Gpr.lowBits,
    `Grass.ISA.X86.Gpr.ofBits, `Grass.ISA.X86.Gpr.rexBitV,
    `Grass.ISA.X86.Rex.of, `Grass.ISA.X86.Rex.promotesTo64,
    `Grass.ISA.X86.Rex.extendsReg, `Grass.ISA.X86.Rex.extendsIndex,
    `Grass.ISA.X86.Rex.extendsBase,
    `Grass.ISA.X86.Displacement.kind, `Grass.ISA.X86.Displacement.size,
    `Grass.ISA.X86.Immediate.size, `Grass.ISA.X86.Immediate.sizeOf,
    `Grass.ISA.X86.InsnEncoding.size, `Grass.ISA.X86.InsnEncoding.escapeByte,
    `Grass.ISA.X86.RegField.bits, `Grass.ISA.X86.RegField.extended,
    -- Encodability predicates: Grass's decision about what it will emit, not a
    -- statement about what the processor does.
    `Grass.ISA.X86.MemOperand.Encodable,
    `Grass.ISA.X86.MemOperand.indexRegister,
    `Grass.ISA.X86.RmEncoding.needsRex, `Grass.ISA.X86.RmEncoding.modrm,
    `Grass.ISA.X86.RmEncoding.rex,
    `Grass.ISA.X86.ByteReg.highCapable, `Grass.ISA.X86.ByteReg.requiresRex,
    `Grass.ISA.X86.ByteReg.encodingNumber ]

/--
Declarations that genuinely model external behaviour and have no citation yet.

**Debt, not a waiver.** Every entry is a `docs/DECISIONS.md` 21 obligation that
has not been discharged. The list is printed on every run and must only shrink;
adding to it is a reviewed admission that a modeled vendor fact went in
uncited.

Most of these are bit-layout constants and the encoder/decoder pair. They are
covered *in substance* by the nine rules in `Grass/ISA/X86/Profile.lean` — the
ModR/M layout rule really is about `ModRm.modDisp8` as much as about
`ModRm.toByte` — but a rule cites one subject, and splitting each rule into its
constituent declarations is citation work nobody has done.
-/
def owed : List Name :=
  [ `Grass.ISA.X86.Gpr.index, `Grass.ISA.X86.Gpr.encodingBits,
    `Grass.ISA.X86.Gpr.isExtended, `Grass.ISA.X86.Gpr.rexBit,
    `Grass.ISA.X86.Width.bits, `Grass.ISA.X86.Width.default64BitMode,
    `Grass.ISA.X86.ModRm.modRegisterDirect, `Grass.ISA.X86.ModRm.modNoDisplacement,
    `Grass.ISA.X86.ModRm.modDisp8, `Grass.ISA.X86.ModRm.modDisp32,
    `Grass.ISA.X86.ModRm.rmSelectsSib, `Grass.ISA.X86.ModRm.rmSelectsRipRelative,
    `Grass.ISA.X86.ModRm.ofByte, `Grass.ISA.X86.Sib.ofByte,
    `Grass.ISA.X86.Sib.indexNone, `Grass.ISA.X86.Sib.baseNone,
    `Grass.ISA.X86.Sib.scaleFactor,
    `Grass.ISA.X86.Scale.bits, `Grass.ISA.X86.Scale.ofBits,
    `Grass.ISA.X86.Scale.factor,
    `Grass.ISA.X86.Rex.bare, `Grass.ISA.X86.Rex.isRexByte,
    `Grass.ISA.X86.Rex.ofByte?,
    `Grass.ISA.X86.RmEncoding.requiredDisp, `Grass.ISA.X86.RmEncoding.requiresSib,
    `Grass.ISA.X86.RmEncoding.WellFormed,
    `Grass.ISA.X86.Displacement.value,
    `Grass.ISA.X86.encodeMem, `Grass.ISA.X86.decodeMem,
    `Grass.ISA.X86.le32, `Grass.ISA.X86.le16,
    `Grass.ISA.X86.Displacement.toBytes, `Grass.ISA.X86.Immediate.toBytes,
    `Grass.ISA.X86.InsnEncoding.toBytes, `Grass.ISA.X86.InsnEncoding.WellFormed,
    `Grass.ISA.X86.encodeMemInsn, `Grass.ISA.X86.movRegImm32,
    `Grass.ISA.X86.leaR64, `Grass.ISA.X86.callMem64,
    `Grass.ISA.X86.movMem32Imm32, `Grass.ISA.X86.movMem64Imm32 ]

/-- The declarations this gate holds the ledger responsible for. -/
def modeledDeclarations : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some midx := env.getModuleIdxFor? n | continue
    let some mname := env.header.moduleNames[midx.toNat]? | continue
    unless auditedModules.contains mname do continue
    if isGenerated n then continue
    if ci.isCtor || ci.isInductive || ci.isTheorem then continue
    if ← Meta.isProp ci.type then continue
    if ← isProjectionFn n then continue
    if ← Meta.isInstance n then continue
    out := out.push n
  return out.qsort (·.toString < ·.toString)

/-- The declaration a subject is anchored to: its longest prefix that names a
real constant. -/
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

/-- Gate C: rules whose basis has not been checked against both manuals.

This used to catch rules claiming `CommonBasis.agreed` about a document nobody
had opened. That is no longer possible: `CommonRule.agreedIsConfirmed` makes it
a type error, so the eight rules that claimed it now carry
`assertedPendingConfirmation` instead. What remains here is a work list --
which rules are still waiting for someone to open a manual -- rather than a
list of unfounded claims. -/
def basisUnconfirmed (l : Ledger) : List Grass.Core.Name :=
  (l.common.filter fun r => !r.basisConfirmed).map (·.subject)

end Grass.Tests.ISA.X86.LedgerAudit

open Lean Elab Command Grass.ISA.X86 Grass.Tests.ISA.X86.LedgerAudit in
run_cmd liftTermElabM do
  let env ← getEnv
  -- Coverage first, for the reason Tools/AxiomAudit.lean gives: a gate over
  -- half the tree is not a gate. An audited module that is not imported here
  -- contributes no declarations and silently narrows the obligation.
  for m in auditedModules do
    unless env.header.moduleNames.contains m do
      logError m!"ledger audit lists {m} as audited but does not import it, so none of its declarations were checked"
  let l := commonProfileLedger
  let subjects :=
    (l.commonSubjects ++ l.refinedSubjects ++ l.excludedSubjects).map
      (fun n => n.text.toName)

  -- Gate A: subjects resolve.
  let anchorFaults := subjects.filterMap fun s =>
    (anchorFault env s).map (fun m => (s, m))
  for (s, m) in anchorFaults do
    logError m!"ledger subject {s} {m}"

  -- Gate B: every modeled declaration is accounted for.
  let modeled ← modeledDeclarations
  let unaccounted := modeled.filter fun d =>
    !(accountedBy env subjects d) && !(notBehaviour.contains d)
      && !(owed.contains d)
  for d in unaccounted do
    logError m!"{d} models external behaviour with no citation, and is in \
neither notBehaviour nor owed. Cite it, or add it to one of those lists under \
review."

  -- Stale entries in either list are their own defect: they make the lists look
  -- like they are doing more work than they are.
  for d in notBehaviour do
    unless modeled.contains d do
      logError m!"notBehaviour lists {d}, which is not a modeled declaration"
  for d in owed do
    unless modeled.contains d do
      logError m!"owed lists {d}, which is not a modeled declaration"

  -- Gate C: a work list, not a violation. `CommonBasis.agreed` can no longer be
  -- written without confirmed anchors, so what is left here is which rules are
  -- still waiting on someone opening a manual.
  let unfounded := basisUnconfirmed l

  -- Counted directly rather than by subtraction. Deriving "cited" as
  -- everything-minus-the-debt folds the 27 waived declarations into it and
  -- reports several times the real number, which is exactly the flattering
  -- arithmetic this gate exists to replace.
  let cited := modeled.filter (accountedBy env subjects ·)
  logInfo m!"ledger audit: {modeled.size} modeled declarations -- \
{cited.size} carry a citation, {owed.length} owed, \
{notBehaviour.length} reviewed as carrying no external behaviour. \
{subjects.length} ledger subjects, all anchoring to real declarations. \
{unfounded.length} rules await a confirmed basis."
