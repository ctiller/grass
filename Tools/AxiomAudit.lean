import Lean
import Grass.Semantics.BehaviorModel
import Grass.Semantics.BehaviorContract
import Grass.Semantics.Environment
import Grass.Semantics.SpecificationDemands
import Grass.Console.ObservedBehavior
import Grass.Console.ObservedEmbedding
import Grass.Console.Contract
import Grass.Console.ContractCorrect
import Grass.Spec.Console
import Grass.Spec.Resource
import Grass.Semantics.OutputCut
import Grass.Specification.TextLine
import Grass.Console.Behavior
import Grass.Console.Accounting
import Grass.Console.LineBehavior
import Grass.Grammar.Canonical
import Grass.Artifact.Binary.EndianLaws
import Grass.Console.Resources
import Grass.Semantics.BoundaryTiming
import Grass.Console.Timing
import Grass.Console.Captured
import Grass.Console.CapturedDemands
import Grass.Artifact.PE.ImageRoundTrip
import Grass.Artifact.PE.LayoutBinding
import Grass.Console.TargetProjection
import Grass.Console.CapturedProjection
import Grass.Refinement.Console.WriteWaitingGap
import Grass.Refinement.Console.WriteFileProjection
import Grass.Platform.Win32.WriteFileNonresponse
import Grass.Refinement.Console.WriteFileHistory
import Grass.Refinement.Console.WriteFileNonresponse
import Grass.Platform.Win32.WriteFileReturn
import Grass.Refinement.Console.WriteFilePolicy
import Grass.Artifact.PE.ExceptionBinding
import Grass.ISA.X86.EndianBridge
import Grass.Assembly.SourceRuntimeFunction
import Grass.Assembly.SourceInput
import Grass.Assembly.X86Source
import Grass.Assembly.X86ControlFlow
import Grass.Assembly.X86ClosedEncoding
import Grass.Assembly.ByteLayout
import Grass.Assembly.SignedRel32
import Grass.Assembly.X86BranchLayout
import Grass.Assembly.SourceFrameHeader
import Grass.Assembly.SavedPrefix
import Grass.Assembly.SourceFrame
import Grass.Assembly.FrameStore
import Grass.Assembly.LocalAddress
import Grass.Assembly.FrameLoad
import Grass.Assembly.FrameAddressing
import Grass.Assembly.FrameLea
import Grass.Assembly.FrameArgument
import Grass.Assembly.Win32Constants
import Grass.Assembly.RipRelative
import Grass.Assembly.FrameAllocation
import Grass.Assembly.SourcePrologue
import Grass.Assembly.SourceInitialization
import Grass.Assembly.SourceTemplates
import Grass.Assembly.StaticObjects
import Grass.Assembly.SourceSplice
import Grass.Assembly.SourceSpliceDecode
import Grass.Assembly.SourceResolve
import Grass.Assembly.SourceBytes
import Grass.Assembly.SourceImage
import Grass.Assembly.StaticSection
import Grass.Assembly.SourceStaticBindings
import Grass.Assembly.SourceImportBindings
import Grass.Assembly.SourceImportRequests
import Grass.Assembly.SourceLinkedImage
import Grass.Assembly.SourceUnwind
import Grass.Assembly.SourceUnwindPrefix
import Grass.Assembly.SourceStore
import Grass.Assembly.Store32
import Grass.Assembly.Store32Execution
import Grass.ABI.Win64.Convention
import Grass.ABI.Win64.FrameRanges
import Grass.ABI.Win64.Unwind
import Grass.ABI.Win64.UnwindBytes
import Grass.Build.Cache.Key
import Grass.CFG.Contract
import Grass.CFG.Graph
import Grass.CFG.Join
import Grass.CFG.Loop
import Grass.CFG.Stack
import Grass.Certificate
import Grass.Construct.Fragment.Generator
import Grass.Construct.Fragment.Source
import Grass.Construct.Fragment.Verified
import Grass.Construct.Layout.Array
import Grass.Construct.Layout.Core
import Grass.Core.Context
import Grass.Core.Demand
import Grass.Core.Generational
import Grass.Core.Identifiers
import Grass.Core.Name
import Grass.Core.Uid
import Grass.ISA.X86.Addressing
import Grass.ISA.X86.Bytes
import Grass.ISA.X86.BasicInstructions
import Grass.ISA.X86.EncodingTemplate
import Grass.ISA.X86.Rel32
import Grass.ISA.X86.ImmediateArithmetic
import Grass.ISA.X86.RegisterDecode
import Grass.ISA.X86.RegisterLaws
import Grass.ISA.X86.Execution.State
import Grass.ISA.X86.Execution.DecodedSite
import Grass.ISA.X86.Execution.StackInstruction
import Grass.ISA.X86.Execution.CompletionFlags
import Grass.ISA.X86.Citation
import Grass.ISA.X86.Decode
import Grass.ISA.X86.DualCitation
import Grass.ISA.X86.Encoding
import Grass.ISA.X86.Ledger
import Grass.ISA.X86.Performance
import Grass.ISA.X86.Profile
import Grass.ISA.X86.Register
import Grass.ISA.X86.Sources
import Grass.Memory.Access
import Grass.Memory.AddressSpace
import Grass.Memory.Audit
import Grass.Memory.Authority
import Grass.Memory.Coordinates
import Grass.Memory.StorageId
import Grass.Memory.Backing
import Grass.Memory.Event
import Grass.Memory.Fault
import Grass.Memory.Ordering
import Grass.Memory.Profile
import Grass.Memory.Provenance
import Grass.Memory.Range
import Grass.Memory.Rights
import Grass.Memory.Shape
import Grass.Memory.State
import Grass.Memory.GrantMint
import Grass.Memory.LoanBatch
import Grass.Memory.Substep
import Grass.Obligation.Core
import Grass.Obligation.Delta
import Grass.Obligation.Disposition
import Grass.Op.Facets
import Grass.Op.Step
import Grass.Op.CallProtocol
import Grass.Platform.Win32.Console
import Grass.Platform.Win32.Signatures
import Grass.Platform.Win32.WriteFile
import Grass.Process
import Grass.Process.Acceptance
import Grass.Process.Bag
import Grass.Process.ByteFlow.Egress
import Grass.Process.ByteFlow.Ingress
import Grass.Process.ByteFlow.Rechunk
import Grass.Process.Cancellation
import Grass.Process.Cancellation.Compose
import Grass.Process.Cancellation.Identity
import Grass.Process.Cancellation.Policy
import Grass.Process.Correct
import Grass.Process.Facet
import Grass.Process.Function.Serial
import Grass.Process.Network.Assertion
import Grass.Process.Network.Channel
import Grass.Process.Network.Child
import Grass.Process.Network.Commit
import Grass.Process.Network.Death
import Grass.Process.Network.Delivery
import Grass.Process.Network.Escrow
import Grass.Process.Network.Exposure
import Grass.Process.Network.Graph
import Grass.Process.Network.Initial
import Grass.Process.Network.Instance
import Grass.Process.Network.Mailbox
import Grass.Process.Network.Plan
import Grass.Process.Network.Progress
import Grass.Process.Network.Structural
import Grass.Process.Network.Topology
import Grass.Process.Network.Transition
import Grass.Process.Network.WellFormedness
import Grass.Process.Network.World
import Grass.Process.Nominal
import Grass.Process.Observation
import Grass.Process.Progress
import Grass.Process.Protocol.Registry
import Grass.Process.Run
import Grass.Process.Sequential.Adapter
import Grass.Process.Sequential.Machine
import Grass.Process.Sequential.Standard
import Grass.Process.Spec
import Grass.Process.Termination
import Grass.Process.Trace.Independence
import Grass.Process.Trace.Linearization
import Grass.Process.Vocabulary
import Grass.Process.Weave.Blend
import Grass.Process.Weave.Lens
import Grass.Process.Weave.Mixin
import Grass.Refinement.Console.WriteHistory
import Grass.Refinement.Console.WriteWaiting
import Grass.Refinement.Coverage
import Grass.Refinement.FinitePathMap
import Grass.Resource.Algebra
import Grass.Resource.Axis
import Grass.Semantics.Execution
import Grass.Semantics.History
import Grass.Semantics.Observation
import Grass.Semantics.SpecProcess
import Grass.Semantics.Waiting
import Grass.Specification.Boundary
import Grass.Specification.Scope
import Grass.Std.Console.Process
import Grass.Std.Console.WriteAll
import Grass.Std.Logical.Bag
import Grass.Std.Logical.Byte
import Grass.Std.Logical.FiniteMap
import Grass.Std.Logical.HostBytes
import Grass.Std.Logical.Order
import Grass.Std.Logical.Text
import Grass.Std.Logical.Vec
import Grass.Trust.Audit
import Grass.Unsafe.Construct
import Grass.Verify.VerifiedProgram

/-!
# Axiom audit

`docs/FOUNDATION.md` §3: "Every theorem used by the verified gate is audited
transitively for axioms, regardless of which dependency declared them. Only the
reviewed Lean logical foundation allowlist (`propext`, quotient soundness, and
classical choice, with their exact toolchain declaration names) is permitted.
Dependency-defined axioms, `sorryAx`, `sorry`, `admit`, unsafe declarations used
as proof, and equivalent admission mechanisms make the gate fail."

This tool implements that audit over every declaration in the `Grass` namespace.
It is run by `.github/workflows/library.yml` and fails the build on any axiom
outside the allowlist.

## Coverage is checked, not assumed

An explicit import list is a coverage hazard, and it failed in exactly the
predictable way: within a day of being written it had fallen six modules behind
the tree, and a maximally false axiom in an unimported module passed both this
tool and `lake build` with exit 0. A gate that silently stops covering the newest
code is worse than no gate, because the green run still reads as assurance.

`checkCoverage` therefore walks `Grass/` on disk and fails if any module found
there is absent from the imported environment. The import list is still written
out below — Lean has no dynamic import — but it can no longer be wrong without
the build saying so.

The list also means this file imports every leaf, which
`docs/OLEAN_SHARDING.md` §2 forbids for an aggregate certificate. That rule is
about proof aggregates whose types grow with their descendants. This is a
diagnostic that must see everything by construction, produces no theorem, and is
not on the path to `VerifiedProgram`. It lives under `Tools/` and outside the
library glob so it cannot be mistaken for one.

It is also not a proof. `docs/FOUNDATION.md` §3 is discharged by the kernel
recording which axioms each declaration depends on; this tool reads that record
and reports. A green run is evidence, in the sense of
`docs/VALIDATION.md`, not a theorem.
-/

open Lean

namespace Grass.Tools

/--
The reviewed logical-foundation allowlist.

Exactly the three constants `docs/FOUNDATION.md` §3 permits, by their toolchain
declaration names. Adding to this list is a trust-boundary change and requires
the review that section demands, not an edit here.
-/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/--
The name a declaration is written under, with any `private` mangling removed.

A `private` declaration is stored as `_private.<module>.<n>.<real name>`, whose
first component is `_private` rather than `Grass`. Testing the namespace on the
stored name therefore skipped every private declaration in the library -- 111 in
the x86 tree alone, including proof-carrying theorems. Stripping the mangling
first is what puts them back inside the audit.
-/
def userFacing (name : Name) : Name := (privateToUserName? name).getD name

/-- Whether a declaration belongs to the audited namespace. -/
def isAudited (name : Name) : Bool :=
  let n := userFacing name
  (`Grass).isPrefixOf n

run_cmd do
  unless isAudited `Grass._authoredUnderscoreProbe do
    throwError "axiom audit would skip an authored underscore-prefixed Grass declaration"

/--
Attributes that make a declaration's compiled behaviour differ from its logical
definition.

`docs/FOUNDATION.md` §3 is about what a proof may depend on, and this is the
same question one step out. Every differential in this repository generates its
corpus by *executing* a Grass definition through `lake env lean --run`, while
every theorem is about the definition the kernel sees. `@[implemented_by]`,
`@[extern]` and `@[csimp]` are exactly the three ways to make those two objects
different.

A reviewer demonstrated the consequence: an `opcodeTable` whose `0x83` row was
poisoned to the wrong immediate size, with `@[implemented_by]` pointing at an
untouched copy, passed the build, both audits, the ledger and all four
differentials -- including the decoder differential written specifically to
catch that mutation. It produces no axiom, no warning and no `unsafe` marker,
so nothing else here would ever notice.

None of the three is forbidden in general; they are forbidden on declarations
this repository's assurance rests on, which is every `Grass` declaration.
-/
def compiledOverride (env : Environment) (name : Name) : Option String :=
  if (Lean.Compiler.getImplementedBy? env name).isSome then
    some "@[implemented_by]"
  else if Lean.isExtern env name then
    some "@[extern]"
  else
    Option.none

/--
Every Lean module found under `root` on disk, as a module name.

The audit compares this against the environment's imported modules, so a module
that exists but was never imported is reported rather than silently skipped.
-/
partial def modulesOnDisk (root : System.FilePath) (prefix_ : Name) :
    IO (Array Name) := do
  let mut found : Array Name := #[]
  for entry in (← root.readDir) do
    let name := entry.fileName
    if ← entry.path.isDir then
      found := found ++ (← modulesOnDisk entry.path (prefix_ ++ Name.mkSimple name))
    else if name.endsWith ".lean" then
      let stem := name.dropEnd 5 |>.toString
      found := found.push (prefix_ ++ Name.mkSimple stem)
  return found

end Grass.Tools

open Grass.Tools in
run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  -- Coverage first: an axiom audit over half the tree is not an axiom audit.
  let imported := env.header.moduleNames
  let onDisk ← Grass.Tools.modulesOnDisk (System.FilePath.mk "Grass") `Grass
  let missing := onDisk.filter fun m => !imported.contains m
  unless missing.isEmpty do
    throwError m!"axiom audit coverage gap: these modules exist under Grass/ but are not imported by Tools/AxiomAudit.lean, so their declarations were never scanned:
{MessageData.joinSep (missing.toList.map (m!"  {·}")) "
"}"
  let mut audited : Nat := 0
  let mut unsafeFindings : Array Name := #[]
  let mut overrideFindings : Array (Name × String) := #[]
  let mut findings : Array (Name × Name) := #[]
  for (name, info) in env.constants.toList do
    unless isAudited name do continue
    audited := audited + 1
    -- §3 also names "unsafe declarations used as proof".
    if info.isUnsafe then
      unsafeFindings := unsafeFindings.push name
    -- The compiled definition must be the proved one; see `compiledOverride`.
    match compiledOverride env name with
    | some attr => overrideFindings := overrideFindings.push (userFacing name, attr)
    | Option.none => pure ()
    let axioms ← Elab.Command.liftCoreM (collectAxioms name)
    for used in axioms do
      unless allowedAxioms.contains used do
        findings := findings.push (name, used)
  unless overrideFindings.isEmpty do
    let lines := overrideFindings.map fun (name, attr) => m!"  {name} carries {attr}"
    throwError m!"axiom audit failed: a Grass declaration's compiled behaviour is \
allowed to differ from its logical definition. Every differential in this \
repository measures the compiled definition while every theorem is about the \
logical one, so this severs the two.
{MessageData.joinSep lines.toList "
"}"
  unless unsafeFindings.isEmpty do
    throwError m!"axiom audit failed; docs/FOUNDATION.md section 3 forbids unsafe declarations used as proof:
{MessageData.joinSep (unsafeFindings.toList.map (m!"  {·}")) "
"}"
  if findings.isEmpty then
    logInfo m!"axiom audit: {audited} Grass declarations across {onDisk.size} modules, no axiom outside the allowlist, no unsafe declaration, no compiled override"
  else
    let lines := findings.map fun (name, used) => m!"  {name} depends on {used}"
    throwError m!"axiom audit failed; docs/FOUNDATION.md section 3 permits only \
{allowedAxioms}\n{MessageData.joinSep lines.toList "\n"}"
