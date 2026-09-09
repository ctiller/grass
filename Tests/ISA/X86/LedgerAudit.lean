import Lean.Elab.Command
import Grass.ISA.X86.Bytes
import Grass.ISA.X86.BasicInstructions
import Grass.ISA.X86.Rel32
import Grass.ISA.X86.ImmediateArithmetic
import Grass.ISA.X86.RegisterDecode
import Grass.ISA.X86.RegisterLaws
import Grass.ISA.X86.EndianBridge
import Grass.ISA.X86.Execution.State
import Grass.ISA.X86.Execution.DecodedSite
import Grass.ISA.X86.Execution.AccessRun
import Grass.ISA.X86.Execution.Fetch
import Grass.ISA.X86.Execution.FetchedEncoding
import Grass.ISA.X86.Execution.MemoryAccess
import Grass.ISA.X86.Execution.MemoryWrite
import Grass.ISA.X86.Execution.ReadValue32
import Grass.ISA.X86.Execution.MemoryMoveNormal
import Grass.ISA.X86.Execution.SubRspNormal
import Grass.ISA.X86.Execution.PushNormal
import Grass.ISA.X86.Execution.AccessFree
import Grass.ISA.X86.Execution.MoveNormal
import Grass.ISA.X86.Execution.AccessPolicy
import Grass.ISA.X86.Execution.ArithmeticNormal
import Grass.ISA.X86.Execution.BranchNormal
import Grass.ISA.X86.Execution.Dispatch
import Grass.ISA.X86.Execution.FetchAttempt
import Grass.ISA.X86.Execution.Instruction
import Grass.ISA.X86.Execution.LeaNormal
import Grass.ISA.X86.Execution.MoveSelection
import Grass.ISA.X86.Execution.ObservedFetch
import Grass.ISA.X86.Execution.PushSavedRead
import Grass.ISA.X86.Execution.RawOutcome
import Grass.ISA.X86.Execution.ReadValue64
import Grass.ISA.X86.Execution.RunFactory
import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.ComputationFactory
import Grass.ISA.X86.Execution.PushFactory
import Grass.ISA.X86.Execution.CallNormal
import Grass.ISA.X86.Execution.CallFactory
import Grass.ISA.X86.Execution.CheckedChoice
import Grass.ISA.X86.Execution.ReturnSlotRead
import Grass.ISA.X86.Execution.ReturnSlotFactory
import Grass.ISA.X86.LinearAddress
import Grass.ISA.X86.Execution.StackInstruction
import Grass.ISA.X86.Execution.CompletionFlags
import Grass.ISA.X86.Decode
import Grass.ISA.X86.Profile
import Grass.ABI.Win64.UnwindBytes
import Grass.ABI.Win64.FrameRanges
import Grass.Platform.Win32.Console
import Grass.Platform.Win32.Signatures
import Grass.Platform.Win32.WriteFile
import Grass.Platform.Win32.WriteFileNonresponse
import Grass.Platform.Win32.WriteFileStabilization
import Grass.Platform.Win32.WriteFileReturn
import Grass.Platform.Win32.LoaderEntry
import Grass.Platform.Win32.LoadedAccess
import Grass.Platform.Win32.LoadedDataAccess
import Grass.Platform.Win32.CpuVocabulary
import Grass.Platform.Win32.CpuPolicy
import Grass.Platform.Win32.ExecutionState
import Grass.Platform.Win32.WriteFileAbi
import Grass.Platform.Win32.WriteFileArguments
import Grass.Platform.Win32.ApiRequest
import Grass.Platform.Win32.WriteFileCallPlan
import Grass.Platform.Win32.WriteFileHandoff
import Grass.Platform.Win32.WriteFilePreservation
import Grass.Platform.Win32.WriteFileCall
import Grass.Platform.Win32.WriteFileCallPreservation
import Grass.Artifact.PE.ImageRoundTrip
import Grass.Artifact.PE.LayoutBinding
import Grass.Artifact.PE.ExceptionBinding
import Grass.Artifact.PE.Imported
import Grass.Disasm.StoreAttempt
import Grass.Disasm.FetchedEntry
import Grass.Disasm.CompletedViolation
import Grass.ISA.X86.Execution.StoreCompletion
import Grass.ISA.X86.Execution.StoreCandidate
import Grass.Disasm.Entry
import Grass.Disasm.CallerObject

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
named only the five x86 encoding modules — so the whole Win64 ABI, Win32 API,
and PE/COFF artifact surface was outside the citation obligation while
`docs/VALIDATION.md` §1 names "API, ABI rule, binary structure" explicitly. A
reviewer injected two false uncited ABI facts into
`Grass/ABI/Win64/Convention.lean` and the summary line came back byte-identical.
The list now covers all four trees this profile owns. It is still a list rather
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
   `Grass.ISA.X86.Addressing, `Grass.ISA.X86.Bytes, `Grass.ISA.X86.BasicInstructions,
   `Grass.ISA.X86.Rel32,
   `Grass.ISA.X86.ImmediateArithmetic,
   `Grass.ISA.X86.RegisterSemantics, `Grass.ISA.X86.RegisterDecode,
   `Grass.ISA.X86.RegisterLaws,
   `Grass.ISA.X86.EndianBridge,
   `Grass.ISA.X86.Execution.State, `Grass.ISA.X86.Execution.DecodedSite,
   `Grass.ISA.X86.Execution.AccessRun, `Grass.ISA.X86.Execution.Fetch,
   `Grass.ISA.X86.Execution.FetchedEncoding,
   `Grass.ISA.X86.Execution.MemoryAccess, `Grass.ISA.X86.Execution.MemoryWrite,
   `Grass.ISA.X86.Execution.ReadValue32,
   `Grass.ISA.X86.Execution.MemoryMoveNormal,
   `Grass.ISA.X86.Execution.SubRspNormal,
   `Grass.ISA.X86.Execution.PushNormal,
   `Grass.ISA.X86.Execution.AccessFree, `Grass.ISA.X86.Execution.MoveNormal,
   `Grass.ISA.X86.Execution.AccessPolicy,
   `Grass.ISA.X86.Execution.ArithmeticNormal, `Grass.ISA.X86.Execution.BranchNormal,
   `Grass.ISA.X86.Execution.Dispatch, `Grass.ISA.X86.Execution.FetchAttempt,
   `Grass.ISA.X86.Execution.Instruction, `Grass.ISA.X86.Execution.LeaNormal,
   `Grass.ISA.X86.Execution.MoveSelection, `Grass.ISA.X86.Execution.ObservedFetch,
   `Grass.ISA.X86.Execution.PushSavedRead, `Grass.ISA.X86.Execution.RawOutcome,
   `Grass.ISA.X86.Execution.ReadValue64, `Grass.ISA.X86.Execution.RunFactory,
   `Grass.ISA.X86.Execution.FetchFactory, `Grass.ISA.X86.Execution.ComputationFactory,
   `Grass.ISA.X86.Execution.PushFactory,
   `Grass.ISA.X86.Execution.CallNormal,
   `Grass.ISA.X86.Execution.CallFactory, `Grass.ISA.X86.Execution.ReturnSlotRead,
   `Grass.ISA.X86.Execution.CheckedChoice,
   `Grass.ISA.X86.Execution.ReturnSlotFactory,
   `Grass.ISA.X86.LinearAddress,
   `Grass.ISA.X86.Execution.StackInstruction, `Grass.ISA.X86.Execution.CompletionFlags,
   `Grass.ISA.X86.Decode,
   `Grass.ABI.Win64.Convention, `Grass.ABI.Win64.FrameRanges, `Grass.ABI.Win64.Unwind,
   `Grass.ABI.Win64.UnwindBytes, `Grass.Platform.Win32.Console,
   `Grass.Platform.Win32.Signatures, `Grass.Platform.Win32.WriteFile,
   `Grass.Platform.Win32.WriteFileNonresponse,
   `Grass.Platform.Win32.WriteFileStabilization,
   `Grass.Platform.Win32.WriteFileResult, `Grass.Platform.Win32.WriteFileReturn,
   `Grass.Platform.Win32.LoaderImage, `Grass.Platform.Win32.LoaderRegion,
   `Grass.Platform.Win32.LoaderEntry,
   `Grass.Platform.Win32.LoadedAccess, `Grass.Platform.Win32.CpuVocabulary,
   `Grass.Platform.Win32.LoadedDataAccess,
   `Grass.Platform.Win32.CpuPolicy,
   `Grass.Platform.Win32.ExecutionState, `Grass.Platform.Win32.WriteFileAbi,
   `Grass.Platform.Win32.WriteFileArguments,
   `Grass.Platform.Win32.ApiRequest,
   `Grass.Platform.Win32.WriteFileCallPlan,
   `Grass.Platform.Win32.WriteFileHandoff,
   `Grass.Platform.Win32.WriteFilePreservation,
   `Grass.Platform.Win32.WriteFileCall,
   `Grass.Platform.Win32.WriteFileCallPreservation,
   `Grass.Artifact.PE.Description, `Grass.Artifact.PE.Layout,
   `Grass.Artifact.PE.Imports, `Grass.Artifact.PE.Validation,
   `Grass.Artifact.PE.Exceptions, `Grass.Artifact.PE.ExceptionReader,
   `Grass.Artifact.PE.ExceptionBinding,
   `Grass.Artifact.PE.HeaderPrefix, `Grass.Artifact.PE.OptionalHeader,
   `Grass.Artifact.PE.SectionTable, `Grass.Artifact.PE.ReaderCore,
   `Grass.Artifact.PE.PrefixReader, `Grass.Artifact.PE.OptionalReader,
   `Grass.Artifact.PE.SectionReader, `Grass.Artifact.PE.ImageWriter,
   `Grass.Artifact.PE.ImageReader, `Grass.Artifact.PE.ImageRoundTrip,
   `Grass.Artifact.PE.LayoutInvariance, `Grass.Artifact.PE.LayoutBinding,
   `Grass.Artifact.PE.Imported, `Grass.Disasm.StoreAttempt,
   `Grass.Disasm.Entry, `Grass.Disasm.CallerObject,
   `Grass.Disasm.FetchedEntry, `Grass.ISA.X86.Execution.StoreCandidate,
   `Grass.Disasm.CompletedViolation, `Grass.ISA.X86.Execution.StoreCompletion]

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
-- Eleven new constructor/operand bindings in BasicInstructions use existing
-- opcode rows. Their decoder roundtrips do not discharge vendor validation.
-- Rel32 adds a branch constructor and its computed size over existing rows;
-- decoder agreement still does not discharge the architecture citation debt.
-- Reviewed additions: three immediate-arithmetic encoding facts and two
-- Win32 signature tables. No existing citation debt is reclassified.
-- WriteFile loan footprint and Prepared's DWORD/CPU profile contract are
-- newly modeled API obligations. Source comments/probes are not ledger citations.
-- Thirteen new register-transfer/flag/operand-selection facts. Manual headings
-- are recorded in the module; formal subject/dual-anchor coverage remains owed.
-- No existing debt is reclassified by this addition.
-- PE/COFF adds 71 format-schema, profile, serializer, and reader obligations.
-- No PE declaration is treated as cited merely because a Lean roundtrip holds.
-- Matched-return adds raw BOOL width, DWORD observation and result conformance.
-- Exception tables add 18 schema, flag, serialization and validation obligations.
-- Seven execution-foundation facts add length/flag/encoding obligations.
-- No prior debt moves to notBehaviour or becomes cited through these tests.
-- The fetched normal SUB RSP constructor adds one instruction-transfer obligation.
-- Thirteen loader/entry, IAT-width, placement and permission commitments.
-- Preferred-base model fixtures and a native sample do not discharge citation debt.
-- The fetched normal register PUSH adds one instruction-transfer obligation.
-- Normal MOV adds its encoding, effect, flags and architectural result obligations.
-- Imported PE field traversal adds readImportedPrefix/readImportedImage and
-- factors readSignatureAndCoff. Microsoft source is recorded in Imported.lean;
-- formal subject/anchor enrollment remains explicit debt, not a citation claim.
-- Imported C7 candidate evidence/check/address/width add four modeled facts.
-- Decoder/encoder reuse does not discharge their separate external enrollment.
-- Entry selection adds eight mapping definitions and its contract type.
-- The vendor URL is provenance; formal ledger anchors remain owed.
-- Reviewed fetched normal SUB RSP adds one transfer obligation.
-- Reviewed PUSH/MOV add five instruction-transfer obligations.
-- The completed-store carrier pins a bounded instruction access contract.
-- Memory MOV completion adds eight architectural value, operand, width, payload,
-- encoding, address, and result obligations. No existing debt is reclassified.
-- Arithmetic, branch, LEA and fixed access dispatch add twenty reviewed obligations.
-- Twelve fixed CPU/ABI obligations, including executable/readable region selection.
-- Six fixed request/stack contracts are newly enrolled; no existing debt moves.
def owedBaseline : Nat := 324

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
-- Nine new representation conversions, derived queries, and internal names.
-- Four lookup-derived opcode selections and checked encoding-template wrappers.
-- Ten WriteFile definitions are internal evidence/transport/sequence operations;
-- Windows footprint and width/profile applicability remain owed separately.
-- Fourteen new structural helpers over explicit semantic and decoder results.
-- Twenty-nine PE coordinate, projection, and supplied-data transformations are
-- implementation plumbing over the separately owed format schema/profile.
-- Two nonresponse consumers derive finite histories or accept a selected
-- external relation; neither asserts Windows adequacy or physical nonresponse.
-- Three new generic definitions derive history events or name selected evidence.
-- Ten exception helpers traverse, project or compare already selected values.
-- Eight execution helpers represent state or select existing decoded constructors.
-- One helper replaces the memory-machine field after a checked fetch.
-- One continuation shift reindexes existing committed edges and histories.
-- Fourteen loader helpers install/compare supplied memory records, scan identity
-- references, project checked header data, and transform finite byte sequences.
-- One access-free receipt projects the already completed memory state.
-- sectionSlicesMatch and checkImportedImage add only exact-data/proof plumbing
-- over the separately owed external parser; neither defines a platform fact.
-- Store operand and productionEncoding are projections/delegation to the
-- separately modeled existing memory operand and encoder, not new ISA rules.
-- Nine caller-factory definitions construct an explicitly declared synthetic
-- state via checked memory doors; they assert no recovered allocator behavior.
-- Reviewed fetch helper replaces only the memory-machine field.
-- Reviewed AccessFree receipt adds one representation helper.
-- Three completed-object helpers transport proven memory equality or compose
-- existing spatial checks; they do not assert a loader or source interpretation.
-- Main adds a reviewed reindexing helper for continuation suffixes.
-- Four memory-completion helpers project or package already selected evidence.
-- This addition moves no existing declaration from owed or cited coverage.
-- Fixed dispatch and access factories add thirty checked structural helpers.
-- Eleven checked carrier projections, loaded-record searches and internal labels.
-- Thirteen custody predicates and checked adapters add no external behavior.
def notBehaviourBaseline : Nat := 272

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
with three flagrantly false uncited ABI facts. The axiom audit and the
declaration-name walk the docstring audit runs -- then a checked-in
meta-program, now generated by the tool itself -- both named the new module,
their disk walks being real, but the ledger did not, so after adding the two
imports those guards demanded, the ledger's summary came back byte-identical
to baseline.

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
   `Grass.ISA.X86.EncodingTemplate]

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
    -- Exact table views, fixed-plan predicates and checked bookkeeping adapters;
    -- they assert no native provider or CPU adequacy beyond their premises.
    `Grass.Platform.Win32.WriteFile.EntryHandoff.after,
    `Grass.Platform.Win32.WriteFile.EntryHandoff.history,
    `Grass.Platform.Win32.WriteFile.EntryHandoff.initialPrefix,
    `Grass.Platform.Win32.WriteFile.EntryHandoff.record,
    `Grass.Platform.Win32.WriteFile.LoanPlan.ReadFootprint,
    `Grass.Platform.Win32.WriteFile.LoanPlan.WriteAt,
    `Grass.Platform.Win32.WriteFile.LoanPlan.WriteFootprint,
    `Grass.Platform.Win32.WriteFile.LoanPlan.requests,
    `Grass.Platform.Win32.WriteFile.ProtocolState,
    `Grass.Platform.Win32.WriteFile.embedPending,
    `Grass.Platform.Win32.WriteFile.entryHandoff?,
    `Grass.Platform.Win32.WriteFile.reachedCall?,
    `Grass.Platform.Win32.WriteFile.selectPending,
    -- Checked protocol projections and loader-table searches contain no new
    -- physical behavior claim. Their underlying profile/ABI facts remain owed.
    `Grass.Platform.Win32.ExecutionState.State.callProtocol?,
    `Grass.Platform.Win32.ExecutionState.State.ControlConsistent,
    `Grass.Platform.Win32.ExecutionState.State.ofCallProtocol,
    `Grass.Platform.Win32.Loader.allocationProvenance,
    `Grass.Platform.Win32.Loader.LoadedImage.codeRoot?,
    `Grass.Platform.Win32.Loader.CodeRoot.provenance,
    `Grass.Platform.Win32.Loader.LoadedImage.stackProvenance?,
    `Grass.Platform.Win32.Loader.LoadedImage.dataRoot?,
    `Grass.Platform.Win32.Loader.DataRoot.provenance,
    `Grass.Platform.Win32.Cpu.dataProvenance?,
    `Grass.Platform.Win32.Cpu.instructionCause,
    `Grass.Platform.Win32.InitializedRegion.allocationRecord,
    `Grass.Platform.Win32.InitializedRegion.backingRecord,
    `Grass.Platform.Win32.MemoryFresh,
    `Grass.Platform.Win32.installInitializedRegion?,
    `Grass.Platform.Win32.Loader.CpuPlacementValid,
    `Grass.Platform.Win32.Loader.CpuPlacementsDisjoint,
    `Grass.Platform.Win32.Loader.HistoryFresh,
    `Grass.Platform.Win32.Loader.ImportTargets,
    `Grass.Platform.Win32.Loader.PlacementValid,
    `Grass.Platform.Win32.Loader.RegionsPresent,
    `Grass.Platform.Win32.Loader.installRegions?,
    `Grass.Platform.Win32.Loader.patchContents,
    `Grass.Platform.Win32.Loader.patchedByte,
    `Grass.Platform.Win32.Loader.preferredBase,
    `Grass.Disasm.CompletedViolation.transportObject,
    `Grass.Disasm.CompletedViolation.fetchedObject,
    `Grass.Disasm.CompletedViolation.check,
    -- Compatibility delegates retain coverage; modeled behavior moved to ISA.
    `Grass.Disasm.StoreAttempt.Error,
    `Grass.Disasm.StoreAttempt.Evidence,
    `Grass.Disasm.StoreAttempt.Evidence.address,
    `Grass.Disasm.StoreAttempt.Evidence.width,
    `Grass.Disasm.StoreAttempt.check,
    -- Equality composition over an existing checked fetch adds no loader rule.
    `Grass.Disasm.FetchedEntry.check,
    `Grass.ISA.X86.Execution.StoreCandidate.Evidence.operand,
    `Grass.ISA.X86.Execution.StoreCandidate.Evidence.productionEncoding,
    `Grass.Disasm.CallerObject.allocSupply,
    `Grass.Disasm.CallerObject.backingSupply,
    `Grass.Disasm.CallerObject.contextSupply,
    `Grass.Disasm.CallerObject.epochSupply,
    `Grass.Disasm.CallerObject.allocation,
    `Grass.Disasm.CallerObject.backing,
    `Grass.Disasm.CallerObject.caller,
    `Grass.Disasm.CallerObject.epoch,
    `Grass.Disasm.CallerObject.check,
    `Grass.Disasm.StoreAttempt.Evidence.operand,
    `Grass.Disasm.StoreAttempt.Evidence.productionEncoding,
    -- Derived accumulated histories and the type of an externally supplied
    -- observation relation, not new Windows behavior facts.
    `Grass.Platform.Win32.WriteFile.InfiniteContinuation.historyAt,
    `Grass.Platform.Win32.WriteFile.InfiniteContinuation.shift,
    `Grass.Platform.Win32.WriteFile.StalledPredicate,
    `Grass.Platform.Win32.WriteFile.History.providerEvents,
    `Grass.Platform.Win32.WriteFile.ReturnInterpretation,
    `Grass.Platform.Win32.WriteFile.CallerInterpretation,
    -- Exact-input/proof projections add no external field interpretation.
    `Grass.Artifact.PE.sectionSlicesMatch,
    `Grass.Artifact.PE.checkImportedImage,
    -- Exception traversal, masks and projections add no format policy.
    `Grass.Artifact.PE.resolveExtent?,
    `Grass.Artifact.PE.writeRuntimeFunctions,
    `Grass.Artifact.PE.writeRuntimeFunctionTable,
    `Grass.Artifact.PE.hasFlag,
    `Grass.Artifact.PE.extentDisjoint,
    `Grass.Artifact.PE.resolveRuntimeFunctions?,
    `Grass.Artifact.PE.runtimeBindingsValid?,
    `Grass.Artifact.PE.ImageLayout.ExceptionsValid,
    `Grass.Artifact.PE.readRuntimeFunctions,
    `Grass.Artifact.PE.ResolvedRuntimeFunction.expectedRecord,
    -- These project supplied spans and payload lengths. Invariance theorems
    -- transport coordinates without adding a format/loader applicability claim.
    `Grass.Artifact.PE.placementSpans,
    `Grass.Artifact.PE.sectionContentLengths,
    `Grass.Artifact.PE.sectionSizes,
    -- PE coordinate arithmetic and supplied-data transformations. The PE field
    -- widths, record writers/readers, and selected profile stay owed below.
    `Grass.Artifact.PE.FileSpan.Disjoint,
    `Grass.Artifact.PE.FileSpan.endOffset,
    `Grass.Artifact.PE.alignUp,
    `Grass.Artifact.PE.RawContiguous,
    `Grass.Artifact.PE.PlacedSection.paddedContents,
    `Grass.Artifact.PE.PlacedSection.expectedSectionHeader,
    `Grass.Artifact.PE.PlacedSection.expectedContents,
    `Grass.Artifact.PE.placeSectionsFrom,
    `Grass.Artifact.PE.placeImageSections,
    `Grass.Artifact.PE.sumRawSizeWith,
    `Grass.Artifact.PE.firstVirtualStartWith,
    `Grass.Artifact.PE.lastVirtualStart,
    `Grass.Artifact.PE.greatestVirtualEnd,
    `Grass.Artifact.PE.resolveSectionLocation?,
    `Grass.Artifact.PE.resolveImageLayout?,
    `Grass.Artifact.PE.ImageLayout.ImportsResolved,
    `Grass.Artifact.PE.ImageLayout.importAddressRva?,
    `Grass.Artifact.PE.ImagePlan.resolveSectionLocation?,
    `Grass.Artifact.PE.ImagePlan.resolveSectionBase?,
    `Grass.Artifact.PE.ImagePlan.expectedImage,
    `Grass.Artifact.PE.writePlacedContentsList,
    `Grass.Artifact.PE.totalRawSize,
    `Grass.Artifact.PE.expectedHeaderPrefix,
    `Grass.Artifact.PE.expectedOptionalHeader,
    `Grass.Artifact.PE.continueRead,
    `Grass.Artifact.PE.withImportSection,
    -- Coordinate projection and metadata-only transport; no claim that a real
    -- Windows allocation satisfies the Prepared applicability contract.
    `Grass.Platform.Win32.WriteFile.Resolved.physical,
    `Grass.Platform.Win32.WriteFile.Resolved.transport,
    `Grass.Platform.Win32.WriteFile.Prepared.transport,
    -- Relations over supplied model bytes/events, not API conformance facts.
    `Grass.Platform.Win32.WriteFile.InputMatches,
    `Grass.Platform.Win32.WriteFile.Confined,
    `Grass.Platform.Win32.WriteFile.Represented,
    -- Delegate to the existing checked machine transition; physical dispatch
    -- and ordering remain separate external realization obligations.
    `Grass.Platform.Win32.WriteFile.Action.Runs,
    -- Pure output projection/fold and Lean's generated history recursion helper.
    `Grass.Platform.Win32.WriteFile.Prefix.output,
    `Grass.Platform.Win32.WriteFile.History.published,
    `Grass.Platform.Win32.WriteFile.History.brecOn.go,
    -- Generic partial-result relations, serialization through the separately
    -- owed bit layout, and accessors over Grass's own semantic record.
    `Grass.ISA.X86.RegisterSemantics.Flags.map,
    `Grass.ISA.X86.RegisterSemantics.Flags.Allows,
    `Grass.ISA.X86.RegisterSemantics.Flags.definedMask,
    `Grass.ISA.X86.RegisterSemantics.Flags.valueBits,
    `Grass.ISA.X86.RegisterSemantics.Effect.destination,
    `Grass.ISA.X86.RegisterSemantics.Effect.Allows,
    `Grass.ISA.X86.RegisterSemantics.Instruction.effect,
    -- Projections/defaults and checked equality search over existing encoders;
    -- architectural operand reconstruction is separately owed below.
    `Grass.ISA.X86.RegisterDecode.rexW,
    `Grass.ISA.X86.RegisterDecode.rexR,
    `Grass.ISA.X86.RegisterDecode.rexB,
    `Grass.ISA.X86.RegisterDecode.selectKinds,
    `Grass.ISA.X86.RegisterDecode.select,
    `Grass.ISA.X86.RegisterDecode.decode,
    `Grass.ISA.X86.RegisterDecode.Result.effect,
    -- Representation updates and checked selection over the existing decoder
    -- and production constructors. These do not execute memory or an instruction.
    `Grass.ISA.X86.Execution.State.statusFlags,
    `Grass.ISA.X86.Execution.State.withGpr,
    `Grass.ISA.X86.Execution.State.withStatusFlags,
    `Grass.ISA.X86.Execution.FetchedSite.afterState,
    `Grass.ISA.X86.Execution.MoveInstruction.destination,
    `Grass.ISA.X86.Execution.DecodedSite.fallthroughRip,
    `Grass.ISA.X86.Execution.StackInstruction.selectPush,
    `Grass.ISA.X86.Execution.StackInstruction.selectSubRsp,
    `Grass.ISA.X86.Execution.StackInstruction.select,
    `Grass.ISA.X86.Execution.StackInstruction.decode,
    -- Structural projections and proof-indexed packaging over an already selected
    -- access completion or memory-MOV constructor.
    `Grass.ISA.X86.Execution.ReadValue32.observed,
    `Grass.ISA.X86.Execution.ReadValue32.bytes,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.Instruction.displacement,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.LoadNormal.read,
    -- Checked packaging, projections and selectors over independently modeled
    -- encoders, decoders, fetches and machine transitions.
    `Grass.ISA.X86.Execution.ArithmeticInstruction.ofRegisterSelection,
    `Grass.ISA.X86.Execution.ArithmeticInstruction.select,
    `Grass.ISA.X86.Execution.ArithmeticInstruction.selectImmediate,
    `Grass.ISA.X86.Execution.BranchInstruction.select,
    `Grass.ISA.X86.Execution.BranchInstruction.tryInstruction,
    `Grass.ISA.X86.Execution.CpuOutcome.state,
    `Grass.ISA.X86.Execution.FetchedSite.toObservedFetch,
    `Grass.ISA.X86.Execution.Instruction.accept,
    `Grass.ISA.X86.Execution.Instruction.encoding?,
    `Grass.ISA.X86.Execution.Instruction.select,
    `Grass.ISA.X86.Execution.Instruction.selectControl,
    `Grass.ISA.X86.Execution.LeaInstruction.accept,
    `Grass.ISA.X86.Execution.LeaInstruction.select,
    `Grass.ISA.X86.Execution.MoveInstruction.select,
    `Grass.ISA.X86.Execution.MoveInstruction.selectImmediate,
    `Grass.ISA.X86.Execution.ObservedFetch.bytes,
    `Grass.ISA.X86.Execution.ObservedFetch.decoded,
    `Grass.ISA.X86.Execution.ObservedFetch.dispatch,
    `Grass.ISA.X86.Execution.ObservedFetch.failureOutcome,
    `Grass.ISA.X86.Execution.ObservedFetch.reachedState,
    `Grass.ISA.X86.Execution.ObservedFetch.toFetchAttempt,
    `Grass.ISA.X86.Execution.ReadValue64.bytes,
    `Grass.ISA.X86.Execution.ReadValue64.observed,
    -- Generic constructors for already selected singleton/access-free generic
    -- operation runs; they add no instruction or target behavior.
    `Grass.ISA.X86.Execution.RunFactory.access,
    `Grass.ISA.X86.Execution.RunFactory.accessFree,
    `Grass.ISA.X86.Execution.RunFactory.accessFreeOperation,
    `Grass.ISA.X86.Execution.RunFactory.instHasOperationFacetsFixedAccessFreeOperation,
    `Grass.ISA.X86.Execution.RunFactory.instHasOperationFacetsSingletonAccessOperation,
    `Grass.ISA.X86.Execution.RunFactory.noFaultPlan,
    `Grass.ISA.X86.Execution.RunFactory.singletonOperation,
    -- Factory packaging and explicit applicability routing over separately
    -- modeled fetch, dispatch, and MOV receipts.
    `Grass.ISA.X86.Execution.ComputationFactory.MoveSuccess.result,
    `Grass.ISA.X86.Execution.ComputationFactory.move,
    -- Constructive SUB RSP routing and projection of its already-modeled receipt.
    `Grass.ISA.X86.Execution.ComputationFactory.SubRspSuccess.result,
    `Grass.ISA.X86.Execution.ComputationFactory.subRsp,
    -- Fixed CALL and return-slot routing delegates to the modeled access and
    -- CALL receipts; projections and read-policy plumbing add no CPU transfer.
    `Grass.ISA.X86.Execution.CallFactory.Success.result,
    `Grass.ISA.X86.Execution.CallFactory.reachedAfterAccess,
    `Grass.ISA.X86.Execution.CallFactory.call,
    `Grass.ISA.X86.Execution.ReturnSlotFactory.readPolicy,
    `Grass.ISA.X86.Execution.ReturnSlotFactory.accessReached,
    `Grass.ISA.X86.Execution.ReturnSlotFactory.read,
    -- Fixed PUSH routing constructs the separately modeled PushNormal receipt;
    -- its failure projection retains the actual already-reached machine.
    `Grass.ISA.X86.Execution.PushFactory.push,
    `Grass.ISA.X86.Execution.PushFactory.reachedAfterAccess,
    `Grass.ISA.X86.Execution.FetchFactory.accessReached,
    `Grass.ISA.X86.Execution.FetchFactory.fetchPolicy,
    -- Decoder-table lookup and packaging of independently checked encoding laws.
    `Grass.ISA.X86.ImmediateArithmetic.operandSpec,
    `Grass.ISA.X86.ImmediateArithmetic.template,
    `Grass.ISA.X86.Rel32.operandSpec,
    `Grass.ISA.X86.Rel32.template,
    -- Representation conversion and queries over the existing immediate type.
    `Grass.ISA.X86.ImmediateArithmetic.Immediate.isa,
    `Grass.ISA.X86.ImmediateArithmetic.Immediate.size,
    `Grass.ISA.X86.ImmediateArithmetic.Immediate.toInt,
    -- Selected inventory, derived table queries, and Grass's internal IAT alias.
    -- The native names and ordered parameter facts themselves remain owed.
    `Grass.Platform.Win32.Signatures.apis,
    `Grass.Platform.Win32.Signatures.argumentCount,
    `Grass.Platform.Win32.Signatures.argumentIndex?,
    `Grass.Platform.Win32.Signatures.importName,
    `Grass.Platform.Win32.Signatures.resolveImport?,
    `Grass.Platform.Win32.Signatures.resolveName?,
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
    -- Reviewed frame construction: selected placement and arithmetic over the
    -- ABI constants. Stack-argument and saved-register placement rules remain
    -- explicit citation debt below; these helpers do not discharge that debt.
    `Grass.ABI.Win64.CallFrameLayout.Admissible,
    `Grass.ABI.Win64.CallFrameLayout.alignUp,
    `Grass.ABI.Win64.CallFrameLayout.localOffset,
    `Grass.ABI.Win64.CallFrameLayout.usedCallAllocationBytes,
    `Grass.ABI.Win64.CallFrameLayout.callAllocationBytes,
    `Grass.ABI.Win64.CallFrameLayout.totalFrameBytes,
    -- Derived range presentations of shadowSpaceBytes, stackArgumentBytes,
    -- and savedRegisterOffset, whose ABI content remains owed. Their laws
    -- relate these presentations to the calculator, not to a new ABI rule.
    `Grass.ABI.Win64.CallFrameLayout.shadowRange,
    `Grass.ABI.Win64.CallFrameLayout.stackArgumentsRange,
    `Grass.ABI.Win64.CallFrameLayout.localRange,
    `Grass.ABI.Win64.CallFrameLayout.paddingRange,
    `Grass.ABI.Win64.CallFrameLayout.callAllocationRange,
    `Grass.ABI.Win64.CallFrameLayout.frameRange,
    `Grass.ABI.Win64.CallFrameLayout.savedRegisterRange,
    -- Fixtures: Spike 1's prologue and a frame-pointer example, which are
    -- values this corpus chose rather than facts about Windows.
    `Grass.ABI.Win64.spike1Prologue, `Grass.ABI.Win64.spike1Layout,
    `Grass.ABI.Win64.spike1SavedRegisters,
    `Grass.ABI.Win64.spike1FrameLayout,
    `Grass.ABI.Win64.spike1CallAllocationBytes,
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
    ]

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
    -- Fixed request widths and callee stack custody retain external ABI debt.
    `Grass.Platform.Win32.ApiRequest,
    `Grass.Platform.Win32.WriteFile.Abi.InitializedReturnQword,
    `Grass.Platform.Win32.WriteFile.Abi.StackPlan,
    `Grass.Platform.Win32.WriteFile.Abi.StackPlan.loanPlan,
    `Grass.Platform.Win32.WriteFile.Abi.StackPlan.requests,
    `Grass.Platform.Win32.WriteFile.Abi.stackRequests,
    -- Fixed operational choices and ABI widths require declaration-level
    -- authority; vendor prose links alone do not close the citation ledger.
    `Grass.Platform.Win32.Cpu.accessFaults,
    `Grass.Platform.Win32.Cpu.vocabulary,
    `Grass.Platform.Win32.Cpu.operationalProfile,
    `Grass.Platform.Win32.Cpu.operationPolicy,
    `Grass.Platform.Win32.Cpu.policy?,
    `Grass.Platform.Win32.Loader.ContainsCodeAddress,
    `Grass.Platform.Win32.Loader.ContainsDataSpan,
    `Grass.Platform.Win32.WriteFile.Abi.returnAddressBytes,
    `Grass.Platform.Win32.WriteFile.Abi.homeSpaceBytes,
    `Grass.Platform.Win32.WriteFile.Abi.overlappedSlotOffset,
    `Grass.Platform.Win32.WriteFile.Abi.InitializedNullQword,
    `Grass.Platform.Win32.WriteFile.Abi.Entry,
    `Grass.Platform.Win32.Loader.EntryMapped,
    `Grass.Platform.Win32.Loader.EnvironmentValid,
    `Grass.Platform.Win32.Loader.ImportPatch.byteAt?,
    `Grass.Platform.Win32.Loader.LoadedImage.initialState,
    `Grass.Platform.Win32.Loader.PatchesValid,
    `Grass.Platform.Win32.Loader.StackPlacementValid,
    `Grass.Platform.Win32.Loader.StackValid,
    `Grass.Platform.Win32.Loader.assignedRegions,
    `Grass.Platform.Win32.Loader.imageRegions,
    `Grass.Platform.Win32.Loader.importPatches?,
    `Grass.Platform.Win32.Loader.importPatchesFrom?,
    `Grass.Platform.Win32.Loader.initialize?,
    `Grass.Platform.Win32.Loader.sectionPermission,
    `Grass.Disasm.Entry.Entry,
    `Grass.Disasm.Entry.virtualExtent,
    `Grass.Disasm.Entry.fileBackedExtent,
    `Grass.Disasm.Entry.fileBackedOffset,
    `Grass.Disasm.Entry.mapsRva,
    `Grass.Disasm.Entry.mappedSections,
    `Grass.Disasm.Entry.selectMappedSection,
    `Grass.Disasm.Entry.sectionBytes,
    `Grass.Disasm.Entry.selectEntry,
    `Grass.ISA.X86.Execution.StoreCandidate.BaseDisplacement.encoded,
    `Grass.ISA.X86.Execution.StoreCandidate.BaseDisplacement.modBits,
    `Grass.ISA.X86.Execution.StoreCandidate.BaseDisplacement.value,
    `Grass.ISA.X86.Execution.StoreCandidate.Evidence,
    `Grass.ISA.X86.Execution.StoreCompletion,
    `Grass.ISA.X86.Execution.StoreCandidate.Evidence.address,
    `Grass.ISA.X86.Execution.StoreCandidate.Evidence.width,
    `Grass.ISA.X86.Execution.StoreCandidate.check,
    -- PE/COFF fixed field widths, offsets, alignments, and characteristic bits
    -- are source-defined format commitments. Their directly derived spans and
    -- the eight-byte section-name representation therefore remain debt too.
    `Grass.Artifact.PE.SectionName,
    `Grass.Artifact.PE.SectionName.ofBytes?,
    `Grass.Artifact.PE.SectionName.write,
    `Grass.Artifact.PE.amd64Machine,
    `Grass.Artifact.PE.executableImageCharacteristics,
    `Grass.Artifact.PE.canonicalPeOffset,
    `Grass.Artifact.PE.peSignatureSize,
    `Grass.Artifact.PE.coffHeaderSize,
    `Grass.Artifact.PE.optionalHeader64Size,
    `Grass.Artifact.PE.sectionHeaderSize,
    `Grass.Artifact.PE.ntHeadersSize,
    `Grass.Artifact.PE.ntHeadersSpan,
    `Grass.Artifact.PE.firstRawOffset,
    `Grass.Artifact.PE.firstSectionRva,
    `Grass.Artifact.PE.canonicalSectionAlignment,
    `Grass.Artifact.PE.canonicalFileAlignment,
    `Grass.Artifact.PE.containsCode,
    `Grass.Artifact.PE.containsInitializedData,
    `Grass.Artifact.PE.importDescriptorSize,
    `Grass.Artifact.PE.importDescriptorTableSize,
    `Grass.Artifact.PE.thunkArraySize,
    -- The import predicates, two-byte hint/name alignment, terminators, and
    -- fixed eight-byte thunk stride select one PE import-table profile.
    `Grass.Artifact.PE.importNameValid,
    `Grass.Artifact.PE.importSymbolsValid,
    `Grass.Artifact.PE.importLibrariesValid,
    `Grass.Artifact.PE.writeHintName,
    `Grass.Artifact.PE.hintNamesSize,
    `Grass.Artifact.PE.hintNameOffsetsFrom,
    `Grass.Artifact.PE.layoutImportLibraryAt,
    `Grass.Artifact.PE.layoutImportLibrariesFrom,
    `Grass.Artifact.PE.layoutImportLibraries,
    `Grass.Artifact.PE.writeImportDescriptor,
    `Grass.Artifact.PE.writeImportDescriptors,
    `Grass.Artifact.PE.writeThunkArray,
    `Grass.Artifact.PE.writeHintNames,
    `Grass.Artifact.PE.writeImportLibraryBlock,
    `Grass.Artifact.PE.writeImportBodiesFrom,
    `Grass.Artifact.PE.writeImportSection,
    `Grass.Artifact.PE.iatSlotRva,
    -- These functions materialize that selected import profile into its
    -- descriptor, IAT, ILT, and hint/name byte representation.
    `Grass.Artifact.PE.importSectionName,
    `Grass.Artifact.PE.makeImportSection,
    `Grass.Artifact.PE.materializeImports,
    `Grass.Artifact.PE.placementFitsU32,
    `Grass.Artifact.PE.placementsFitU32,
    -- Writable and resolved-location contracts put PE RVA/file-width bounds
    -- directly in fields; the structure enrollment above keeps them visible.
    `Grass.Artifact.PE.ImageLayout.Writable,
    `Grass.Artifact.PE.ResolvedSectionLocation,
    `Grass.Artifact.PE.writeCanonicalDosHeader,
    `Grass.Artifact.PE.writePeSignature,
    `Grass.Artifact.PE.writeImageCoffHeader,
    -- Header, optional-header, and section-table serializers assert the exact
    -- PE record schema and field order.
    `Grass.Artifact.PE.writeHeaderPrefixLeading,
    `Grass.Artifact.PE.writeHeaderPrefixTrailing,
    `Grass.Artifact.PE.writeHeaderPrefix,
    `Grass.Artifact.PE.writeDataDirectory,
    `Grass.Artifact.PE.writeDataDirectories,
    `Grass.Artifact.PE.writeOptionalHeader,
    `Grass.Artifact.PE.writeSectionHeader,
    `Grass.Artifact.PE.writeSectionTableList,
    `Grass.Artifact.PE.writeSectionTable,
    `Grass.Artifact.PE.writeUnpaddedHeaders,
    `Grass.Artifact.PE.writeAlignedHeaders,
    `Grass.Artifact.PE.writeImage,
    `Grass.Artifact.PE.prepareImage,
    -- Parsed records and readers accept the same PE schema. The selected
    -- records are explicitly enrolled before the structure filter.
    `Grass.Artifact.PE.ParsedHeaderPrefix,
    `Grass.Artifact.PE.readHeaderPrefix,
    `Grass.Artifact.PE.readSignatureAndCoff,
    `Grass.Artifact.PE.readImportedPrefix,
    `Grass.Artifact.PE.readImportedImage,
    `Grass.Artifact.PE.ParsedOptionalHeader,
    `Grass.Artifact.PE.readOptionalHeader,
    `Grass.Artifact.PE.ParsedSectionHeader,
    `Grass.Artifact.PE.readSectionHeader,
    `Grass.Artifact.PE.readSectionHeaders,
    `Grass.Artifact.PE.readSectionContents,
    `Grass.Artifact.PE.supportedImageHeader,
    `Grass.Artifact.PE.readImage,
    -- Synchronous WriteFile's input-read/output-write footprint and four-byte
    -- DWORD out-slot are vendor facts; Prepared also restricts CPU placement,
    -- no-wrap and disjointness as a selected profile, whose applicability is
    -- still external. No loan or probe result discharges those obligations.
    `Grass.Platform.Win32.WriteFile.Request.loans,
    `Grass.Platform.Win32.WriteFile.DwordAt,
    `Grass.Platform.Win32.WriteFile.ReturnResult,
    `Grass.Platform.Win32.WriteFile.ReturnResult.Conforms,
    -- PE exception record schema, flags, bounded resolution and profile checks.
    `Grass.Artifact.PE.ParsedRuntimeFunction,
    `Grass.Artifact.PE.resolveSectionExtent?,
    `Grass.Artifact.PE.resolveRuntimeFunction?,
    `Grass.Artifact.PE.writeRuntimeFunction,
    `Grass.Artifact.PE.sectionReadable,
    `Grass.Artifact.PE.sectionExecutable,
    `Grass.Artifact.PE.sectionDiscardable,
    `Grass.Artifact.PE.sectionWritable,
    `Grass.Artifact.PE.sectionInitializedData,
    `Grass.Artifact.PE.sectionContainsCode,
    `Grass.Artifact.PE.codeSectionValid?,
    `Grass.Artifact.PE.metadataSectionValid?,
    `Grass.Artifact.PE.runtimeFunctionsAscending?,
    `Grass.Artifact.PE.runtimeBindingValid?,
    `Grass.Artifact.PE.exceptionTableValid,
    `Grass.Artifact.PE.ImageLayout.exceptionDirectory,
    `Grass.Artifact.PE.readRuntimeFunction,
    `Grass.Artifact.PE.readRuntimeTable,
    `Grass.Platform.Win32.WriteFile.Prepared,
    `Grass.ISA.X86.RegisterSemantics.Flags.bits,
    `Grass.ISA.X86.RegisterSemantics.Flags.fromBits,
    `Grass.ISA.X86.RegisterSemantics.Flags.equal?,
    `Grass.ISA.X86.RegisterSemantics.Flags.above?,
    `Grass.ISA.X86.RegisterSemantics.parity,
    `Grass.ISA.X86.RegisterSemantics.arithmeticFlags,
    `Grass.ISA.X86.RegisterSemantics.logicalFlags,
    `Grass.ISA.X86.RegisterSemantics.narrow,
    `Grass.ISA.X86.RegisterSemantics.evaluate,
    `Grass.ISA.X86.RegisterSemantics.evaluateImmediate,
    `Grass.ISA.X86.RegisterSemantics.Instruction.encoding,
    `Grass.ISA.X86.RegisterSemantics.Instruction.registersAfter,
    `Grass.ISA.X86.RegisterDecode.reconstruct,
    -- Bounded execution foundation: architectural length/bit positions and
    -- completed flag transfers retain debt until declaration-level attachment.
    -- Source inspection and representation tests do not settle that attachment.
    `Grass.ISA.X86.Execution.DecodedSite.check,
    `Grass.ISA.X86.Execution.SubRspNormal.result,
    `Grass.ISA.X86.Execution.PushNormal.result,
    `Grass.ISA.X86.Execution.completedMoveRflags,
    `Grass.ISA.X86.Execution.MoveInstruction.encoding,
    `Grass.ISA.X86.Execution.MoveInstruction.effect,
    `Grass.ISA.X86.Execution.MoveNormal.result,
    -- Newly modeled address, arithmetic, branch and LEA behavior. Selector
    -- plumbing is reviewed separately above; these declarations carry the
    -- architectural operation, address, encoding or result content.
    `Grass.ISA.X86.Execution.AddressPlan.descriptor,
    `Grass.ISA.X86.Execution.AddressPlan.offset,
    `Grass.ISA.X86.Execution.planAddress,
    `Grass.ISA.X86.Execution.ArithmeticInstruction.destination,
    `Grass.ISA.X86.Execution.ArithmeticInstruction.effect,
    `Grass.ISA.X86.Execution.ArithmeticInstruction.encoding,
    `Grass.ISA.X86.Execution.ArithmeticNormal.result,
    `Grass.ISA.X86.Execution.BranchInstruction.displacement,
    `Grass.ISA.X86.Execution.BranchInstruction.encoding,
    `Grass.ISA.X86.Execution.BranchInstruction.kind,
    `Grass.ISA.X86.Execution.BranchInstruction.taken,
    `Grass.ISA.X86.Execution.BranchNormal.result,
    `Grass.ISA.X86.Execution.BranchNormal.target,
    `Grass.ISA.X86.Execution.completedBranchRflags,
    `Grass.ISA.X86.Execution.LeaInstruction.baseValue,
    `Grass.ISA.X86.Execution.LeaInstruction.effectiveAddress,
    `Grass.ISA.X86.Execution.LeaInstruction.encoding?,
    `Grass.ISA.X86.Execution.LeaInstruction.operand,
    `Grass.ISA.X86.Execution.LeaNormal.result,
    `Grass.ISA.X86.Execution.ReadValue64.value,
    -- The normal fetch factory's lookahead and footprint determine the actual
    -- execute-read extent; the resulting fetch therefore remains architecture debt.
    `Grass.ISA.X86.Execution.FetchFactory.lookahead,
    `Grass.ISA.X86.Execution.FetchFactory.footprint,
    `Grass.ISA.X86.Execution.FetchFactory.fetch,
    -- Conditional indirect CALL register transfer and actual target interpretation.
    `Grass.ISA.X86.Execution.CallNormal.result,
    -- Unmasked linear-address width, canonical ranges and nonwrapping spans.
    `Grass.ISA.X86.LinearAddressMode.width,
    `Grass.ISA.X86.Canonical,
    `Grass.ISA.X86.CanonicalSpan,
    `Grass.ISA.X86.Execution.StackInstruction.encoding,
    `Grass.ISA.X86.Execution.statusMask,
    `Grass.ISA.X86.Execution.resumeMask,
    `Grass.ISA.X86.Execution.completedPushRflags,
    `Grass.ISA.X86.Execution.completedSubStatus,
    `Grass.ISA.X86.Execution.completedSubRflags,
    -- Normal memory MOV semantics: value decoding, operand/width/payload/encoder
    -- selection, effective address, and the two architectural result states.
    `Grass.ISA.X86.Execution.ReadValue32.value,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.Instruction.operand,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.Instruction.width,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.Instruction.payload?,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.Instruction.encode?,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.Instruction.effectiveAddress,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.StoreNormal.result,
    `Grass.ISA.X86.Execution.MemoryMoveNormal.LoadNormal.result,
    `Grass.ISA.X86.ImmediateArithmetic.Immediate.opcode,
    `Grass.ISA.X86.ImmediateArithmetic.Kind.extension,
    `Grass.ISA.X86.ImmediateArithmetic.encode,
    `Grass.Platform.Win32.Signatures.apiName,
    `Grass.Platform.Win32.Signatures.parameters,
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
    -- New frame rules: stack-passed arguments occupy eight-byte slots; saved
    -- register positions follow the downward stack in reverse push order.
    `Grass.ABI.Win64.CallFrameLayout.stackArgumentBytes,
    `Grass.ABI.Win64.CallFrameLayout.savedRegisterOffset,
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
    `Grass.ISA.X86.BasicInstructions.Width.rexW,
    `Grass.ISA.X86.BasicInstructions.regReg,
    `Grass.ISA.X86.BasicInstructions.push,
    `Grass.ISA.X86.BasicInstructions.movRegReg,
    `Grass.ISA.X86.BasicInstructions.movReg32Mem,
    `Grass.ISA.X86.BasicInstructions.testRegReg,
    `Grass.ISA.X86.BasicInstructions.cmpRegReg,
    `Grass.ISA.X86.BasicInstructions.addRegReg,
    `Grass.ISA.X86.BasicInstructions.subRegReg,
    `Grass.ISA.X86.BasicInstructions.xorRegReg,
    `Grass.ISA.X86.BasicInstructions.ud2,
    `Grass.ISA.X86.Rel32.encode,
    `Grass.ISA.X86.Rel32.encodedSize,
    -- The opcode table is the largest single block of uncited vendor fact in
    -- the tree: every row asserts what follows an opcode in the byte stream.
    `Grass.ISA.X86.opcodeTable, `Grass.ISA.X86.decodeInsn,
    `Grass.ISA.X86.decodeOperands ]

/-- The declarations this gate holds the ledger responsible for. -/
def modeledDeclarations : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some midx := env.getModuleIdxFor? n | continue
    let some mname := env.header.moduleNames[midx.toNat]? | continue
    unless auditedModules.contains mname do continue
    if ← isGenerated n then continue
    -- These selected contract records embed external widths, PE field schemas,
    -- or address-profile bounds in their fields. Include each type explicitly
    -- rather than letting the generic structure filter hide the obligation.
    -- This exception adds coverage; it exempts no future declaration.
    if n == ``Grass.ISA.X86.Execution.StoreCompletion ||
        n == ``Grass.Disasm.Entry.Entry ||
        n == ``Grass.ISA.X86.Execution.StoreCandidate.Evidence ||
        n == ``Grass.Platform.Win32.WriteFile.Abi.StackPlan ||
        n == ``Grass.Platform.Win32.WriteFile.Abi.InitializedReturnQword ||
        n == ``Grass.Platform.Win32.ApiRequest ||
        n == ``Grass.Platform.Win32.WriteFile.Abi.Entry ||
        n == ``Grass.Platform.Win32.WriteFile.Prepared ||
        n == ``Grass.Platform.Win32.WriteFile.ReturnResult ||
        n == ``Grass.Artifact.PE.SectionName ||
        n == ``Grass.Artifact.PE.ParsedHeaderPrefix ||
        n == ``Grass.Artifact.PE.ParsedOptionalHeader ||
        n == ``Grass.Artifact.PE.ParsedSectionHeader ||
        n == ``Grass.Artifact.PE.ParsedRuntimeFunction ||
        n == ``Grass.Artifact.PE.ResolvedSectionLocation then
      out := out.push (userFacing n)
      continue
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
                ("Grass/Platform", `Grass.Platform), ("Grass/Artifact/PE", `Grass.Artifact.PE)] do
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
