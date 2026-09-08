import Lean.Elab.Command
import Grass.ISA.X86.Bytes
import Grass.ISA.X86.Decode
import Grass.ISA.X86.Profile
import Grass.ABI.Win64.UnwindBytes
import Grass.Platform.Win32.Console
import Grass.Platform.Win32.Profile
import Grass.Platform.Win32.Coff
import Grass.Platform.Win32.CoffLayout
import Grass.Platform.Win32.CoffSymbol
import Grass.Platform.Win32.CoffStrings
import Grass.Platform.Win32.CoffPdata
import Grass.Platform.Win32.CoffXdata
import Grass.Platform.Win32.CoffAux
import Grass.Platform.Win32.CoffWellFormed
import Grass.Platform.Win32.CoffText

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

`auditedModules` is a hand-written list, and for most of this file's life it
named only the five x86 encoding modules — so the whole Win64 ABI and Win32 API
surface, 58 behaviour-modelling declarations, was outside the citation
obligation entirely while `docs/VALIDATION.md` §1 names "API, ABI rule, binary
structure" explicitly. A reviewer injected two false uncited ABI facts into
`Grass/ABI/Win64/Convention.lean` and the summary line came back byte-identical.
The list now covers all three trees this profile owns. It is still a list rather
than a disk walk, which is the hazard `Tools/AxiomAudit.lean` solves properly;
closing that here is an open obligation.

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
  it is printed on every run and must only shrink, which `owedBaseline` now
  enforces. It did not before: a reviewer added a name and every gate stayed
  green, and that was the escape hatch that let a poisoned `opcodeTable` past
  the whole suite. `docs/VALIDATION.md` §7's ratchet discipline is the model —
  "Removing the resulting gate requires review explaining why the original
  finding can no longer recur."

The three are disjoint and their sizes add to the number of modeled
declarations. That is checked, because the summary line used to read as a
partition and was not — a reviewer found 6 + 48 + 35 against 88 modeled
declarations, `decodeMem` being counted as cited *and* listed as debt.

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
   `Grass.ISA.X86.Addressing, `Grass.ISA.X86.Bytes, `Grass.ISA.X86.Decode,
   `Grass.ABI.Win64.Convention, `Grass.ABI.Win64.Unwind,
   `Grass.ABI.Win64.UnwindBytes, `Grass.Platform.Win32.Console,
   `Grass.Platform.Win32.Profile, `Grass.Platform.Win32.Coff,
   `Grass.Platform.Win32.CoffLayout,
   `Grass.Platform.Win32.CoffSymbol,
   `Grass.Platform.Win32.CoffStrings,
   `Grass.Platform.Win32.CoffPdata,
   `Grass.Platform.Win32.CoffXdata,
   `Grass.Platform.Win32.CoffAux,
   `Grass.Platform.Win32.CoffWellFormed,
   `Grass.Platform.Win32.CoffText]

/--
The number of entries `owed` was last reviewed at.

The header has always said the debt "must only shrink", citing
`docs/VALIDATION.md` section 7's ratchet. Nothing enforced it, and a reviewer
demonstrated the consequence twice over: adding one name kept every gate green,
and that was the escape hatch that let a poisoned `opcodeTable` through -- the
ledger objected to the new declaration, the reviewer added the one line the
ledger's own rules prescribe, and it went quiet.

Raising this is a reviewed edit, which is the visibility the ratchet is for.
-/
def owedBaseline : Nat := 138

/--
The number of entries `notBehaviour` was last reviewed at.

`owedBaseline` alone ratchets the debt and not the permanent waiver beside it,
so moving an entry from `owed` to `notBehaviour` satisfies it. A reviewer moved
all ninety-three -- `opcodeTable`, `decodeInsn`, `le64`, `encodeMem`, every
Win64 ABI constant -- and this audit reported "0 owed, 145 reviewed as carrying
no external behaviour" and built green. The whole citation debt discharged to
zero without a citation, with a summary line reading better than the truth.

The first attempt at a fix ratcheted the *sum* of the two lists, and did not
work: the sum is exactly invariant under the move it was meant to stop.
Reclassifying `opcodeTable` still passed. Ratcheting `notBehaviour` on its own
is what catches it, and it is the obviously right thing in hindsight --
`notBehaviour` is a *permanent* claim, so it has more reason to be ratcheted
than `owed` does, not less.

Both lists are now capped separately. A declaration can leave either only by
acquiring a citation.
-/
def notBehaviourBaseline : Nat := 82

/--
Classes whose instances say how a type is decided, printed or defaulted, rather
than anything about a processor or an API.

`Meta.isInstance` used to skip *every* instance, and a reviewer put a false
Win64 ABI constant inside `instance redZoneInstance : HasRedZone Unit := ⟨128⟩`
in an audited module and watched it disappear. An ABI fact wearing an `instance`
is still an ABI fact; only these structural classes are exempt, and the list is
reviewed rather than open-ended.
-/
def structuralClasses : List Name :=
  [``Decidable, ``DecidableEq, ``DecidablePred, ``Repr, ``Inhabited, ``BEq,
   ``LawfulBEq, ``ToString, ``Hashable, ``Ord, ``Nonempty, ``Subsingleton]

/--
Modules under the audited roots that model nothing external.

`auditedModules` is a list, and a reviewer added `Grass/ABI/Win64/RedZone.lean`
with three flagrantly false uncited ABI facts. The axiom audit and
`Tools/DeclNames.lean` both named the new module -- their disk walks are real --
but the ledger did not, so after adding the two imports those guards demanded,
the ledger's summary came back byte-identical to baseline.

The walk below closes that. Every `.lean` file under `Grass/ISA/X86`,
`Grass/ABI` and `Grass/Platform` must appear in `auditedModules` or here, and a
new one appears in neither, so it fails until someone decides which it is.

One caveat, because it is the kind that makes a gate quietly useless. This runs
in a `run_cmd`, and `lake build` caches the result -- adding a file elsewhere in
the tree replays the cached run and the walk does not happen. `.github/workflows/
library.yml` invokes this file directly with `lake env lean` rather than through
`lake build`, which is what makes the check load-bearing; that step is not a
convenience.

The entries are the citation machinery itself and the profile that records
citations. None models a processor or an API: a `Citation` record makes no claim
about hardware, and `Performance.lean` is a framework with no `TimingFact` for a
real instruction in it.
-/
def notModelling : List Name :=
  [`Grass.ISA.X86.Citation, `Grass.ISA.X86.DualCitation,
   `Grass.ISA.X86.Sources, `Grass.ISA.X86.Ledger,
   `Grass.ISA.X86.Profile, `Grass.ISA.X86.Performance,
   -- The two authoring facades. They declare nothing at all, so there
   -- is no declaration under them that could owe a citation; the
   -- shards they front are classified individually above and here.
   `Grass.ISA.X86, `Grass.Platform.Win32]

/--
Every Lean module found under `root` on disk, as a module name.

The same walk `Tools/AxiomAudit.lean` performs, and for the same reason: a
hand-written module list is a coverage claim nobody checks.
-/
partial def modulesOnDisk (root : System.FilePath) (prefix_ : Name) :
    IO (Array Name) := do
  let mut found : Array Name := #[]
  for entry in (← root.readDir) do
    let name := entry.fileName
    if ← entry.path.isDir then
      found := found ++ (← modulesOnDisk entry.path (prefix_ ++ Name.mkSimple name))
    else if name.endsWith ".lean" then
      found := found.push (prefix_ ++ Name.mkSimple (name.dropEnd 5 |>.toString))
  return found

/-- Compiler-generated names that are not authored declarations. -/
def generatedSuffixes : List Name :=
  [`rec, `recOn, `casesOn, `below, `brecOn, `ibelow, `binductionOn, `elim,
   `noConfusion, `noConfusionType, `ctorIdx, `toCtorIdx, `ctorElim,
   `ctorElimType, `ofNat, `injEq, `mk,
   `sizeOf_spec, `decEq, `repr, `default, `eq_def, `induct, `fun_cases]

/--
The name a declaration is written under, with any `private` mangling removed.

A `private` declaration is stored as `_private.<module>.<n>.<real name>`.
`Name.isInternal` treats that as internal, so the decoder's five private
helpers -- `takeByte`, `takeDisp`, `takeImm`, `takeLe32`, `takeLe64` -- were
never counted as modeled, though each reads instruction bytes and each is
exactly the kind of declaration this ledger exists to account for.

`Tools/AxiomAudit.lean` had the same defect and the same fix.
-/
def userFacing (n : Name) : Name := (privateToUserName? n).getD n

/--
Whether a name was produced by elaboration rather than written.

One principle, applied twice: **a compiler helper hangs off something**. The
elaborator names what it generates after the declaration it generated it from,
so `FrameSpec._sizeOf_1`, `Gpr.default` and `separated._f` all have a parent
that is itself a constant. An authored declaration does not -- `_redZoneBytes`
and `redZone.default` sit directly in a namespace, with nothing above them for
the elaborator to have derived them from.

That replaces two spelling tests a reviewer walked straight through, both in one
file and both carrying false Win64 ABI facts into an audited module. The suffix
test was `generatedSuffixes.any (·.isSuffixOf n)`, so `def redZone.default` and
`def redZone.mk` were skipped for ending in words that `deriving` also uses. And
`Name.isInternal` treats *any* component beginning with an underscore as
internal, so `def _redZoneBytes` was skipped for its first character. The
summary line came back byte-identical to baseline for all three.

Macro scopes are kept as their own test, because those really do mean the
elaborator made it and carry no parent to consult.

This is still a heuristic about names, and the honest form would ask the
environment for a declaration's origin. Lean does not expose that; declaration
ranges point at the `deriving` clause for derived instances, so they do not
separate them either. Recorded as an open obligation.
-/
def isGenerated (n : Name) : MetaM Bool := do
  if n.hasMacroScopes then return true
  match n with
  | .str parent last =>
      let env ← getEnv
      let parentIsConstant := (env.find? parent).isSome
      -- An underscore-prefixed or reserved-suffix name is a helper only when
      -- there is a constant for it to be a helper *of*.
      -- `match_1`, `eq_1`, `proof_1` and their `.splitter`s are elaboration
      -- products of the declaration they hang off, and carry no author-written
      -- name. Checked over every component, not just the last, because the
      -- helpers nest: `f.match_1.splitter`.
      if n.components.any fun c =>
          ["match_", "eq_", "proof_", "sunfold", "induct_"].any (c.toString.startsWith ·)
        then return true
      if last.startsWith "_" || generatedSuffixes.any (·.toString == last) then
        return parentIsConstant || (← Meta.isInstance parent)
      return false
  | _ => return false


/--
Declarations reviewed and found to carry no claim about a processor.

A permanent claim, one line of reasoning each. Anything here is asserting that a
reader could not be misled by its absence from the trust ledger.
-/
def notBehaviour : List Name :=
  [
    -- `Xmm.all` is a list of Grass constructors, exactly as `Gpr.all` is; the
    -- architectural fact is the numbering, which `Xmm.index` carries in
    -- `owed`. It was put in `owed` alongside `index` when the XMM file
    -- landed, which a reviewer flagged as the wrong bucket by this file's own
    -- rule -- and noted that the wrong bucket happened to need one reviewed
    -- baseline bump where the right one needs two. That is the move this
    -- ratchet exists to catch, so it is recorded rather than quietly fixed.
    `Grass.ISA.X86.Xmm.all,
    -- The platform selection itself. Choosing Windows 10, x64 and documented
    -- APIs is a project decision recorded in `docs/DECISIONS.md` 16, not a
    -- claim about how Windows behaves; the external content it implies is the
    -- pair of widths in `owed` below.
    `Grass.Platform.Win32.decision16,
    `Grass.Platform.Win32.Profile.FollowsDecision16,
    -- Win64 and Win32: Grass's own constructions over the ABI types. The
    -- external content they are built from is in `owed` below.
    `Grass.ABI.Win64.Ascends, `Grass.ABI.Win64.ascends,
    `Grass.ABI.Win64.PdataSection.Separated,
    `Grass.ABI.Win64.PdataSection.separated,
    `Grass.ABI.Win64.Layout.WellFormed, `Grass.ABI.Win64.Layout.codeBytes,
    `Grass.ABI.Win64.Layout.offsets, `Grass.ABI.Win64.Layout.prologue,
    `Grass.ABI.Win64.UnwindInfo.mk?, `Grass.ABI.Win64.SearchablePdata.mk?,
    `Grass.ABI.Win64.Prologue.Encodable, `Grass.ABI.Win64.Prologue.slots,
    `Grass.ABI.Win64.Prologue.stackDelta,
    `Grass.ABI.Win64.Prologue.establishesFramePointer,
    `Grass.ABI.Win64.Prologue.frameSpecIs,
    `Grass.ABI.Win64.RuntimeFunction.Nonempty,
    `Grass.ABI.Win64.RuntimeFunction.PointsOutside,
    `Grass.ABI.Win64.volatileRegisters, `Grass.ABI.Win64.nonvolatileRegisters,
    `Grass.ABI.Win64.rspAfterPrologue,
    -- Fixtures: Spike 1's prologue and a frame-pointer example, which are
    -- values this corpus chose rather than facts about Windows.
    `Grass.ABI.Win64.spike1Prologue, `Grass.ABI.Win64.spike1Layout,
    `Grass.ABI.Win64.spike1UnwindInfo, `Grass.ABI.Win64.framePointerLayout,
    `Grass.Platform.Win32.GetStdHandleResult.WellFormed,
    `Grass.Platform.Win32.UsableHandle.mk?,
    `Grass.Platform.Win32.ExcessWriteCount,
 -- Enumerations of Grass's own types. `Gpr.all` is a list of Grass
    -- constructors; the architectural fact is the numbering, which
    -- `Gpr.index` carries and which is cited.
    `Grass.ISA.X86.Gpr.all, `Grass.ISA.X86.Width.all,
    -- Grass-internal accessors over Grass's own representation. Each is a
    -- projection of a cited fact, not a separate claim about the machine.
    `Grass.ISA.X86.Gpr.ofIndex, `Grass.ISA.X86.Gpr.lowBits,
    `Grass.ISA.X86.Gpr.ofBits, `Grass.ISA.X86.Gpr.rexBitV,
    `Grass.ISA.X86.Rex.of,
    `Grass.ISA.X86.Displacement.kind, `Grass.ISA.X86.Displacement.size,
    `Grass.ISA.X86.Immediate.size, `Grass.ISA.X86.Immediate.sizeOf,
    `Grass.ISA.X86.InsnEncoding.size,
    `Grass.ISA.X86.RegField.bits, `Grass.ISA.X86.RegField.extended,
    -- One-line adapters that lift an already-cited byte layout to "this field's
    -- bytes, or none". Whether the field is *present* is a vendor fact, and it
    -- is `RmEncoding.requiresSib` and `dispKindFor`, both listed as owed.
    `Grass.ISA.X86.InsnEncoding.rexBytes, `Grass.ISA.X86.InsnEncoding.escapeBytes,
    `Grass.ISA.X86.InsnEncoding.modrmBytes, `Grass.ISA.X86.InsnEncoding.sibBytes,
    -- Decoder plumbing over Grass's own types, and the diagnostics vocabulary.
    `Grass.ISA.X86.findSpec, `Grass.ISA.X86.plusRegRows,
    `Grass.ISA.X86.MatchesSpec, `Grass.ISA.X86.specShapeFor,
    -- Encodability predicates: Grass's decision about what it will emit, not a
    -- statement about what the processor does.
    `Grass.ISA.X86.MemOperand.Encodable,
    `Grass.ISA.X86.MemOperand.indexRegister,
    `Grass.ISA.X86.RmEncoding.needsRex, `Grass.ISA.X86.RmEncoding.modrm,
    `Grass.ISA.X86.RmEncoding.rex,
        -- The COFF layout arithmetic. None of these asserts anything about the
    -- format: `dataSize` and `relocSize` are sums over sections this model
    -- already holds, `dataOffsets` and `relocOffsets` are running totals over
    -- an arrangement `Object.toBytes` chose rather than one COFF requires, and
    -- `relocationBytes` only concatenates records whose own layout is cited
    -- through `Relocation.toBytes` in `owed`. A vendor document would have
    -- nothing to say about any of them.
    `Grass.Platform.Win32.Coff.Object.dataSize,
    `Grass.Platform.Win32.Coff.Object.relocSize,
    `Grass.Platform.Win32.Coff.Section.relocationBytes,
    `Grass.Platform.Win32.Coff.dataOffsets,
    `Grass.Platform.Win32.Coff.relocOffsets,
    -- The string table's arithmetic, which asserts nothing the format decides.
    -- `stringEntries` concatenates entries whose own shape is cited through
    -- `stringEntry`; `stringEntriesSize` sums their lengths; `stringOffsets`
    -- is a running total over that same sum. The `+ 1` in the last two is the
    -- terminator `stringEntry` already accounts for, not a second claim about
    -- it.
    `Grass.Platform.Win32.Coff.stringEntries,
    `Grass.Platform.Win32.Coff.stringEntriesSize,
    `Grass.Platform.Win32.Coff.stringOffsets,
    -- Where this profile puts the two tables, which the format does not
    -- decide. COFF locates the symbol table by `pointerToSymbolTable` and the
    -- string table by following it, so any arrangement the header describes is
    -- legal; `tailBytes` and `symbolTableOffset` record the one chosen here.
    -- A vendor document would not contradict a different choice.
    `Grass.Platform.Win32.Coff.Object.tailBytes,
    `Grass.Platform.Win32.Coff.Object.symbolTableOffset,
    -- `.pdata` assembly, which asserts nothing beyond the three rows above.
    -- `pdataBytes` concatenates entries, `pdataRelocations` numbers them by
    -- position, and `pdataSection` puts name, bytes, relocations and flags in
    -- one record so a caller cannot pair a section's data with someone else's
    -- relocations.
    `Grass.Platform.Win32.Coff.pdataBytes,
    `Grass.Platform.Win32.Coff.pdataRelocations,
    `Grass.Platform.Win32.Coff.pdataSection,
    -- `.xdata` assembly. `xdataBlock` applies the padding `alignPad` decides,
    -- `xdataBytes` concatenates blocks, `xdataOffsets` is a running total over
    -- them, and `xdataSection` collects name, bytes, relocations and flags.
    -- The arrangement of blocks within the section is this profile's, not the
    -- format's: COFF locates each `UNWIND_INFO` by the addend a `.pdata` entry
    -- carries, so any order those addends describe is legal.
    `Grass.Platform.Win32.Coff.xdataBlock,
    `Grass.Platform.Win32.Coff.xdataBytes,
    `Grass.Platform.Win32.Coff.xdataOffsets,
    `Grass.Platform.Win32.Coff.xdataSection,
    -- `plain` is this profile's choice of an all-zero COMDAT triple, which the
    -- format neither requires nor forbids; `sectionSymbolBytes` concatenates a
    -- symbol with its auxiliary record, and both halves are cited above.
    `Grass.Platform.Win32.Coff.AuxSectionDefinition.plain,
    `Grass.Platform.Win32.Coff.symbolRecordCount,
    `Grass.Platform.Win32.Coff.symbolTableBytes,
    -- A one-line restatement of `ResolvableIn` at the entry level, carrying no
    -- fact the row above does not.
    `Grass.Platform.Win32.Coff.SymbolEntry.SectionResolvable,
    -- `.text` assembly. `relocation?` and `displacementRelocations?` apply
    -- `ripRelative?`, whose rule is cited above; `textSection?` combines that
    -- with the range check; `dotText` is a name literal used by this module's
    -- own theorems, which need a closed term to evaluate.
    `Grass.Platform.Win32.Coff.DisplacementSite.relocation?,
    `Grass.Platform.Win32.Coff.displacementRelocations?,
    `Grass.Platform.Win32.Coff.textSection?,
    `Grass.Platform.Win32.Coff.dotText ]

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
  [
    -- The XMM register file's numbering, added for UWOP_SAVE_XMM128. Which
    -- register is number six is an architectural fact like any other in this
    -- ledger, and it carries no citation yet: DECISIONS 15 wants the
    -- Intel/AMD intersection, and the AMD side is unretrievable (see
    -- `Grass.ISA.X86.Sources`), so an anchor added now could not be confirmed.
    `Grass.ISA.X86.Xmm.index,
    -- Which XMM registers a callee must preserve. An external ABI fact, and
    -- it was previously a bare `6` inside UnwindOp.Encodable with no
    -- declaration to carry it -- so the fact was real, load-bearing and
    -- absent from this ledger entirely. Naming it is what put it here.
    `Grass.ABI.Win64.xmmVolatility,
    -- The two ceilings of UWOP_ALLOC_LARGE. Both are external facts about the
    -- unwind encoding rather than choices: 524280 is what the 16-bit scaled
    -- field reaches, and 4294967288 is what the unscaled form reaches, which
    -- ml64 confirms by refusing 2^32 with A2156.
    `Grass.ABI.Win64.UnwindOp.largeAllocScaledMax,
    `Grass.ABI.Win64.UnwindOp.largeAllocRawMax,
    -- Where an unwind code may sit relative to the instruction it describes.
    -- An external rule about how the unwinder reads the array -- a code takes
    -- effect after its instruction, except a machine frame, which precedes
    -- every instruction -- rather than a construction of Grass's own.
    `Grass.ABI.Win64.PlacedOp.OffsetPlaced,
    -- The Win32 handle and pointer widths. A reviewer of the platform profile
    -- pointed out that these are external ABI facts wearing the clothes of a
    -- project selection: `docs/DECISIONS.md` 16 fixes x64, but it says nothing
    -- about how wide a `HANDLE` is, and a consistently wrong pair would pass
    -- every gate here. They owe a citation like any other machine fact.
    `Grass.Platform.Win32.TargetAbi.handleBits,
    `Grass.Platform.Win32.TargetAbi.pointerBits,
    -- Architectural facts that were in `notBehaviour` and should not have been.
    -- A reviewer pointed at the sharpest case: `ByteReg.Encodable` is one of the
    -- six cited declarations and is *defined from* `highCapable` and
    -- `requiresRex`, so the ledger cited the derived predicate while
    -- permanently waiving the two constants carrying its content. Which
    -- registers have a legacy high-byte form, which low-byte forms need a REX
    -- prefix, that a high-byte register's number is base+4, what each REX bit
    -- extends, and that the two-byte escape is 0F -- every one is a statement
    -- about the processor, not a choice this corpus made. `notBehaviour` is a
    -- permanent waiver, which makes misfiling worse than owing.
    `Grass.ISA.X86.ByteReg.highCapable, `Grass.ISA.X86.ByteReg.requiresRex,
    `Grass.ISA.X86.ByteReg.encodingNumber,
    `Grass.ISA.X86.Rex.promotesTo64, `Grass.ISA.X86.Rex.extendsReg,
    `Grass.ISA.X86.Rex.extendsIndex, `Grass.ISA.X86.Rex.extendsBase,
    `Grass.ISA.X86.InsnEncoding.escapeByte,
    -- Win64 ABI. `docs/DECISIONS.md` 16 fixes the baseline at Win32 x64 and
    -- `docs/VALIDATION.md` section 1 names "API, ABI rule, binary structure"
    -- explicitly, so these owe citations exactly as the instruction encodings
    -- do. None carries one: `Grass.ISA.X86.DualCitation` is closed over
    -- intel | amd, so there is no citation type for a Microsoft document and
    -- no Microsoft `SourceDocument` is registered. That is the debt.
    `Grass.ABI.Win64.volatility, `Grass.ABI.Win64.argumentRegister,
    `Grass.ABI.Win64.argumentRegisters,
    `Grass.ABI.Win64.registerArgumentCount,
    `Grass.ABI.Win64.shadowSpaceBytes, `Grass.ABI.Win64.stackAlignment,
    `Grass.ABI.Win64.entryMisalignment, `Grass.ABI.Win64.AlignedForCall,
    `Grass.ABI.Win64.regNibble,
    `Grass.ABI.Win64.UnwindOp.opcode, `Grass.ABI.Win64.UnwindOp.opInfo,
    `Grass.ABI.Win64.UnwindOp.slots, `Grass.ABI.Win64.UnwindOp.stackDelta,
    `Grass.ABI.Win64.UnwindOp.Encodable,
    `Grass.ABI.Win64.UnwindOp.SmallAllocEncodable,
    `Grass.ABI.Win64.UnwindOp.LargeAllocEncodable,
    `Grass.ABI.Win64.Prologue.codes, `Grass.ABI.Win64.Prologue.countOfCodes,
    `Grass.ABI.Win64.Prologue.arraySlots,
    `Grass.ABI.Win64.Layout.padding, `Grass.ABI.Win64.FrameSpec.declared,
    `Grass.ABI.Win64.UnwindInfo.version, `Grass.ABI.Win64.UnwindInfo.toBytes,
    `Grass.ABI.Win64.UnwindTail.flags, `Grass.ABI.Win64.UnwindTail.handlerRva,
    `Grass.ABI.Win64.UnwindTail.toBytes, `Grass.ABI.Win64.PlacedOp.toBytes,
    `Grass.ABI.Win64.RuntimeFunction.toBytes,
    `Grass.ABI.Win64.PdataSection.WellFormed,
    `Grass.ABI.Win64.PdataSection.toBytes,
    `Grass.ABI.Win64.SearchablePdata.toBytes,
    -- Win32 console API.
    `Grass.Platform.Win32.StdHandleId.value,
    `Grass.Platform.Win32.GetStdHandleResult.invalidHandleValue,
    `Grass.Platform.Win32.GetStdHandleResult.returnValue,
    `Grass.Platform.Win32.Allowed, `Grass.Platform.Win32.successStatus,
    `Grass.Platform.Win32.failureStatus,
    `Grass.ISA.X86.Gpr.index, `Grass.ISA.X86.Gpr.encodingBits,
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
    `Grass.ISA.X86.Rex.ofByte?, `Grass.ISA.X86.rexWSet,
    -- The decoder's private byte readers. Each says how many bytes a field
    -- occupies and in what order, which is a statement about the encoding and
    -- not about Grass. They were invisible until `userFacing` above stopped
    -- `Name.isInternal` hiding them.
    `Grass.ISA.X86.takeByte, `Grass.ISA.X86.takeDisp, `Grass.ISA.X86.takeImm,
    `Grass.ISA.X86.takeLe32, `Grass.ISA.X86.takeLe64,
    `Grass.ISA.X86.le64, `Grass.ISA.X86.OpcodeSpec.immSizeFor,
    `Grass.ISA.X86.RmEncoding.requiredDisp, `Grass.ISA.X86.RmEncoding.requiresSib,
    `Grass.ISA.X86.dispKindFor,
    `Grass.ISA.X86.RmEncoding.WellFormed,
    `Grass.ISA.X86.Displacement.value,
    `Grass.ISA.X86.encodeMem,
    `Grass.ISA.X86.le32, `Grass.ISA.X86.le16,
    `Grass.ISA.X86.Displacement.toBytes, `Grass.ISA.X86.Immediate.toBytes,
    `Grass.ISA.X86.InsnEncoding.toBytes, `Grass.ISA.X86.InsnEncoding.WellFormed,
    `Grass.ISA.X86.encodeMemInsn, `Grass.ISA.X86.movRegImm64, `Grass.ISA.X86.movRegImm32,
    `Grass.ISA.X86.leaR64, `Grass.ISA.X86.callMem64,
    `Grass.ISA.X86.movMem32Imm32, `Grass.ISA.X86.movMem64Imm32,
    -- The opcode table is the largest single block of uncited vendor fact in
    -- the tree: every row asserts what follows an opcode in the byte stream.
    `Grass.ISA.X86.opcodeTable, `Grass.ISA.X86.decodeInsn,
    `Grass.ISA.X86.decodeOperands,
    -- The COFF object records. Every one of these is a Microsoft PE/COFF
    -- specification fact rather than a choice: the machine code `0x8664`, the
    -- three relocation type codes, and the field order, field width and
    -- padding of the file header, the section header, the section name and
    -- the relocation. They are uncited for a different reason than the x86
    -- rows above -- there the AMD half of the DECISIONS 15 intersection is
    -- unretrievable, whereas here the anchor is a single vendor document that
    -- has simply not been added to `Grass.ISA.X86.Sources` yet, because that
    -- module is an *ISA* source list and a file-format specification is not an
    -- instruction-set reference. Where a PE/COFF anchor belongs is a real
    -- question and not one this list should answer silently.
    --
    -- They are checked against a real object file today -- see
    -- `Tests/Platform/Win32/CoffFixture.lean`, which holds the twenty, forty
    -- and ten byte records `ml64` actually wrote -- so the debt here is a
    -- missing citation, not a missing measurement.
    `Grass.Platform.Win32.Coff.Machine.code,
    `Grass.Platform.Win32.Coff.RelocationType.code,
    -- Which member of the REL32 family a RIP-relative displacement needs,
    -- which the format decides by counting the instruction bytes that follow
    -- the displacement field: REL32 with none, REL32_n with n. Measured --
    -- an imm32 gets REL32_4, an imm8 gets REL32_1, an imm16 gets REL32_2 --
    -- and choosing wrongly resolves the address off by exactly that many
    -- bytes, silently.
    `Grass.Platform.Win32.Coff.RelocationType.ripRelative?,
    `Grass.Platform.Win32.Coff.Relocation.toBytes,
    `Grass.Platform.Win32.Coff.SectionName.mk?,
    `Grass.Platform.Win32.Coff.SectionName.toBytes,
    `Grass.Platform.Win32.Coff.SectionHeader.toBytes,
    `Grass.Platform.Win32.Coff.FileHeader.toBytes,
    `Grass.Platform.Win32.Coff.FileHeader.sectionTableOffset,
    -- The layout constants, which are the same kind of fact one level up.
    -- `headerSize` is twenty plus forty per section, and both numbers are the
    -- record sizes the format fixes; `relocationSize` is ten per entry for the
    -- same reason. `toBytes` places the file header at offset zero with the
    -- section table immediately after it, which the format requires -- the
    -- *rest* of its arrangement is a choice this profile makes and owes
    -- nothing. `fileHeader` and `sectionHeaders` assert what each field means,
    -- which is the format's claim and not this model's.
    `Grass.Platform.Win32.Coff.Object.headerSize,
    `Grass.Platform.Win32.Coff.Object.toBytes,
    `Grass.Platform.Win32.Coff.Object.fileHeader,
    `Grass.Platform.Win32.Coff.Object.sectionHeaders,
    `Grass.Platform.Win32.Coff.Section.relocationSize,
    -- The symbol table records, and every one of these is the format speaking
    -- rather than this model choosing. `Symbol.toBytes` is the eighteen-byte
    -- record and its field order. `SectionNumber.code` carries the three
    -- reserved values -- zero for undefined, -1 absolute, -2 debug -- which are
    -- meanings the format assigns, not encodings this profile picked.
    -- `SymbolName.toBytes` is the two readings of one eight-byte field, and
    -- `leadingZeros` is the format's own discriminator between them: four zero
    -- bytes means string-table offset. `short?` refuses the names that would be
    -- misread, which is a consequence of that same rule.
    --
    -- Checked against a real object -- see
    -- `Tests/Platform/Win32/CoffFixture.lean`, which holds three eighteen-byte
    -- records `ml64` wrote, covering both name forms and two of the three
    -- reserved section numbers -- so the debt is a missing citation rather than
    -- a missing measurement.
    `Grass.Platform.Win32.Coff.Symbol.toBytes,
    `Grass.Platform.Win32.Coff.SectionNumber.code,
    `Grass.Platform.Win32.Coff.SymbolName.toBytes,
    `Grass.Platform.Win32.Coff.SymbolName.leadingZeros,
    `Grass.Platform.Win32.Coff.SymbolName.short?,
    -- The string table's two format facts. `stringEntry` appends the NUL that
    -- terminates a name -- the format supplies no length, so the terminator is
    -- the only thing that ends a string. `stringTableBytes` writes the
    -- four-byte size that *includes itself*, which is the quirk a writer gets
    -- wrong by four and which a reader uses to find the end of the object.
    `Grass.Platform.Win32.Coff.stringEntry,
    `Grass.Platform.Win32.Coff.stringTableBytes,
    -- `.pdata`'s three format facts. `PdataEntry.toBytes` is the twelve-byte
    -- entry and which of its fields hold addends -- zero, the function length,
    -- and the unwind offset. `PdataEntry.relocations` is the structure the
    -- bytes cannot carry: three ADDR32NB fix-ups at 0, 4 and 8, with the first
    -- two naming the function and the third the shared unwind section.
    -- `pdataCharacteristics` is the section's flag word.
    --
    -- Measured on two objects, not one. A single function cannot distinguish a
    -- twelve-byte stride from an eight-byte one, and cannot show that
    -- UnwindInfoAddress carries a nonzero offset -- both were caught only by
    -- assembling a second function. See `Tests/Platform/Win32/CoffFixture.lean`.
    `Grass.Platform.Win32.Coff.PdataEntry.toBytes,
    `Grass.Platform.Win32.Coff.PdataEntry.relocations,
    `Grass.Platform.Win32.Coff.pdataCharacteristics,
    -- `.xdata`'s two external facts. `alignPad` encodes the requirement that
    -- every `UNWIND_INFO` begin on a four-byte boundary, which the format
    -- imposes and this profile does not get to choose.
    -- `xdataCharacteristics` is the section's flag word, and it is *not*
    -- `.pdata`'s: measured, they differ in the alignment field, `ALIGN_4BYTES`
    -- against `ALIGN_8BYTES`. The model carried `.pdata`'s word in both places
    -- until an object was read for it.
    `Grass.Platform.Win32.Coff.alignPad,
    `Grass.Platform.Win32.Coff.xdataCharacteristics,
    -- The auxiliary section-definition record: eighteen bytes, and which of
    -- them hold the section's size and relocation count. The format states
    -- both numbers twice, once in the section header and once here, and the
    -- field order and the three unused tail bytes are its decision.
    `Grass.Platform.Win32.Coff.AuxSectionDefinition.toBytes,
    -- Two facts about how the symbol table is counted, both the format's.
    -- `SymbolEntry.count` says an auxiliary record is a table entry in its own
    -- right, which is why both measured objects report fifteen symbols when
    -- they define ten. `SymbolEntry.toBytes` derives `numberOfAuxSymbols` from
    -- what follows, which is the field's meaning: it tells a reader how many
    -- entries to skip, and a relocation's symbol index counts every one of
    -- them.
    `Grass.Platform.Win32.Coff.SymbolEntry.count,
    `Grass.Platform.Win32.Coff.SymbolEntry.toBytes,
    -- What it means for an object's internal references to resolve, which the
    -- format decides and this profile does not. `ResolvableIn` encodes that
    -- sections are numbered from one and that zero, -1 and -2 name no section;
    -- `RelocationsInRange` encodes that a relocation's `symbolIndex` is an
    -- index into the symbol table's *records*. Both are conditions a linker
    -- imposes, and neither produces a diagnostic when violated -- which is why
    -- they are stated rather than assumed.
    `Grass.Platform.Win32.Coff.SectionNumber.ResolvableIn,
    `Grass.Platform.Win32.Coff.Section.RelocationsInRange,
    -- `.text`'s two facts. `InRange` is what it means for a displacement site
    -- to fit: four bytes of field plus the instruction bytes after it, all
    -- inside the section -- a linker writing past the end is not diagnosed by
    -- anything. `textCharacteristics` is the section's flag word as `ml64`
    -- writes it: code, executable, readable.
    `Grass.Platform.Win32.Coff.DisplacementSite.InRange,
    `Grass.Platform.Win32.Coff.textCharacteristics ]

/-- The declarations this gate holds the ledger responsible for. -/
def modeledDeclarations : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some midx := env.getModuleIdxFor? n | continue
    let some mname := env.header.moduleNames[midx.toNat]? | continue
    unless auditedModules.contains mname do continue
    if ← isGenerated n then continue
    if ci.isCtor || ci.isInductive || ci.isTheorem then continue
    if ← Meta.isProp ci.type then continue
    -- An instance of a structural class says how a type is decided or printed.
    -- An instance of anything else can carry a modeled fact; see
    -- `structuralClasses`.
    if ← Meta.isInstance n then
      let cls ← Meta.isClass? ci.type
      if cls.any structuralClasses.contains then continue
    if ← isProjectionFn n then continue
    out := out.push (userFacing n)
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
  -- And every module under the audited roots is classified, so a new file
  -- cannot be invisible to this gate the way `RedZone.lean` was.
  for root in [("Grass/ISA/X86", `Grass.ISA.X86), ("Grass/ABI", `Grass.ABI),
               ("Grass/Platform", `Grass.Platform)] do
    let onDisk ← modulesOnDisk (System.FilePath.mk root.1) root.2
    for m in onDisk do
      unless auditedModules.contains m || notModelling.contains m do
        logError m!"{m} exists under {root.1} but is in neither auditedModules \
nor notModelling, so nothing decides whether its declarations owe citations"
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

  -- The three buckets must partition, or the summary line is arithmetic that
  -- does not add up. It did not: a reviewer noticed 6 + 48 + 35 = 89 against 88
  -- modeled declarations, because `decodeMem` was counted as cited *and* listed
  -- as debt. A summary that reads as a partition and is not is the same class
  -- of defect as the subtraction this gate replaced.
  for d in owed do
    if notBehaviour.contains d then
      logError m!"{d} is in both owed and notBehaviour; a declaration owes a \
citation or is reviewed as owing none, not both"
  for d in (owed ++ notBehaviour) do
    if accountedBy env subjects d then
      logError m!"{d} carries a citation but is also listed as owed or \
notBehaviour; remove it from that list"

  -- The debt may shrink and must not grow silently. `docs/VALIDATION.md`
  -- section 7's ratchet, which the header claimed and nothing enforced: a
  -- reviewer added one name to `owed` and every gate stayed green.
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
{unfounded.length} rules await a confirmed basis. \n{l.unconfirmedAnchors.length} of {l.citations.length} anchors are unconfirmed. \
{(l.releaseBlockers.map (fun d => d.id.text)).eraseDups} is the release-blocker set (docs/VALIDATION.md section 1: a dead location under a referenceOnly policy blocks release)"
