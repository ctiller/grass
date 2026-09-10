import Grass.ABI.Win64.Convention
import Grass.ABI.Win64.FrameRanges
import Grass.ABI.Win64.Unwind
import Grass.ABI.Win64.UnwindBytes
import Grass.Artifact.Binary.Endian
import Grass.Artifact.Binary.EndianLaws
import Grass.Artifact.Binary.LEB128
import Grass.Artifact.Binary.LittleEndian
import Grass.Artifact.Binary.Primitive
import Grass.Artifact.Binary.ReaderCore
import Grass.Artifact.Binary.Realization
import Grass.Artifact.ELF.Header
import Grass.Artifact.ELF.Target
import Grass.Artifact.Flat.Target
import Grass.Artifact.PE.Description
import Grass.Artifact.PE.ExceptionBinding
import Grass.Artifact.PE.ExceptionReader
import Grass.Artifact.PE.Exceptions
import Grass.Artifact.PE.HeaderPrefix
import Grass.Artifact.PE.ImageReader
import Grass.Artifact.PE.ImageRoundTrip
import Grass.Artifact.PE.ImageWriter
import Grass.Artifact.PE.Imported
import Grass.Artifact.PE.Imports
import Grass.Artifact.PE.Layout
import Grass.Artifact.PE.LayoutBinding
import Grass.Artifact.PE.LayoutInvariance
import Grass.Artifact.PE.OptionalHeader
import Grass.Artifact.PE.OptionalReader
import Grass.Artifact.PE.PrefixReader
import Grass.Artifact.PE.ReaderCore
import Grass.Artifact.PE.SectionReader
import Grass.Artifact.PE.SectionTable
import Grass.Artifact.PE.Target
import Grass.Artifact.PE.Target.Image
import Grass.Artifact.PE.Target.Imports
import Grass.Artifact.PE.Target.Names
import Grass.Artifact.PE.Validation
import Grass.Artifact.Wasm.Expr
import Grass.Artifact.Wasm.Section
import Grass.Artifact.Wasm.Sections
import Grass.Artifact.Wasm.Strings
import Grass.Artifact.Wasm.Target
import Grass.Assembly.Lower.AArch64
import Grass.Assembly.Lower.Layout
import Grass.Assembly.Lower.Lowering
import Grass.Assembly.Lower.Wasm
import Grass.Assembly.Lower.X86
import Grass.Assembly.Lower.X86Lengths
import Grass.Assembly.Syntax.AST
import Grass.Assembly.Syntax.Parser
import Grass.Assembly.Syntax.Wellformed
import Grass.Build.Cache.Key
import Grass.CFG.Contract
import Grass.CFG.Graph
import Grass.CFG.Join
import Grass.CFG.Loop
import Grass.CFG.Stack
import Grass.Certificate
import Grass.Console.OutcomePolicy
import Grass.Console.Resources
import Grass.Console.WriteLineContract
import Grass.Construct.Fragment.Generator
import Grass.Construct.Fragment.Source
import Grass.Construct.Fragment.Verified
import Grass.Construct.Layout.Array
import Grass.Construct.Layout.Core
import Grass.Core.CallIdentity
import Grass.Core.Context
import Grass.Core.Demand
import Grass.Core.Generational
import Grass.Core.Identifiers
import Grass.Core.Name
import Grass.Core.Uid
import Grass.Device.Vulkan
import Grass.Device.WebGPU
import Grass.Disasm.CallerObject
import Grass.Disasm.CompletedViolation
import Grass.Disasm.Entry
import Grass.Disasm.FetchedEntry
import Grass.Disasm.Linear
import Grass.Disasm.Spatial
import Grass.Disasm.StoreAttempt
import Grass.Grammar.Binary
import Grass.Grammar.Canonical
import Grass.Grammar.Core
import Grass.Grammar.Endian
import Grass.Grammar.Realization
import Grass.ISA.AArch64.Control
import Grass.ISA.AArch64.Sources
import Grass.ISA.AArch64.Target
import Grass.ISA.AArch64.Target.Encoding
import Grass.ISA.AArch64.Target.Native
import Grass.ISA.AArch64.Target.State
import Grass.ISA.AArch64.Target.Step
import Grass.ISA.SPIRV.Composite
import Grass.ISA.Wasm.Invocation
import Grass.ISA.Wasm.LocalStep
import Grass.ISA.Wasm.Module
import Grass.ISA.Wasm.Target
import Grass.ISA.Wasm.Target.Encode
import Grass.ISA.Wasm.Target.Instr
import Grass.ISA.Wasm.Target.LEB128
import Grass.ISA.Wasm.Target.Native
import Grass.ISA.Wasm.Target.State
import Grass.ISA.Wasm.Types
import Grass.ISA.X86.Addressing
import Grass.ISA.X86.BasicInstructions
import Grass.ISA.X86.Bytes
import Grass.ISA.X86.Citation
import Grass.ISA.X86.Decode
import Grass.ISA.X86.DualCitation
import Grass.ISA.X86.Encoding
import Grass.ISA.X86.EncodingTemplate
import Grass.ISA.X86.EndianBridge
import Grass.ISA.X86.Execution.AccessFree
import Grass.ISA.X86.Execution.AccessPolicy
import Grass.ISA.X86.Execution.AccessRun
import Grass.ISA.X86.Execution.ArithmeticNormal
import Grass.ISA.X86.Execution.BodyComputationFactory
import Grass.ISA.X86.Execution.BranchNormal
import Grass.ISA.X86.Execution.CallFactory
import Grass.ISA.X86.Execution.CallNormal
import Grass.ISA.X86.Execution.CheckedChoice
import Grass.ISA.X86.Execution.CheckedStep
import Grass.ISA.X86.Execution.CompletionFlags
import Grass.ISA.X86.Execution.ComputationFactory
import Grass.ISA.X86.Execution.DecodedSite
import Grass.ISA.X86.Execution.Dispatch
import Grass.ISA.X86.Execution.Fetch
import Grass.ISA.X86.Execution.FetchAttempt
import Grass.ISA.X86.Execution.FetchFactory
import Grass.ISA.X86.Execution.FetchedEncoding
import Grass.ISA.X86.Execution.Instruction
import Grass.ISA.X86.Execution.LeaNormal
import Grass.ISA.X86.Execution.MemoryAccess
import Grass.ISA.X86.Execution.MemoryMoveFactory
import Grass.ISA.X86.Execution.MemoryMoveNormal
import Grass.ISA.X86.Execution.MemoryMoveSelection
import Grass.ISA.X86.Execution.MemoryWrite
import Grass.ISA.X86.Execution.MoveNormal
import Grass.ISA.X86.Execution.MoveSelection
import Grass.ISA.X86.Execution.ObservedFetch
import Grass.ISA.X86.Execution.PushFactory
import Grass.ISA.X86.Execution.PushNormal
import Grass.ISA.X86.Execution.PushSavedRead
import Grass.ISA.X86.Execution.RawOutcome
import Grass.ISA.X86.Execution.ReadValue32
import Grass.ISA.X86.Execution.ReadValue64
import Grass.ISA.X86.Execution.ReturnSlotFactory
import Grass.ISA.X86.Execution.ReturnSlotRead
import Grass.ISA.X86.Execution.RunFactory
import Grass.ISA.X86.Execution.StackInstruction
import Grass.ISA.X86.Execution.State
import Grass.ISA.X86.Execution.StoreCandidate
import Grass.ISA.X86.Execution.StoreCompletion
import Grass.ISA.X86.Execution.SubRspNormal
import Grass.ISA.X86.ImmediateArithmetic
import Grass.ISA.X86.Ledger
import Grass.ISA.X86.Profile
import Grass.ISA.X86.Register
import Grass.ISA.X86.RegisterDecode
import Grass.ISA.X86.RegisterLaws
import Grass.ISA.X86.RegisterSemantics
import Grass.ISA.X86.Rel32
import Grass.ISA.X86.Sources
import Grass.ISA.X86.Target
import Grass.ISA.X86.Target.Core.Operands
import Grass.ISA.X86.Target.Core.Prefixes
import Grass.ISA.X86.Target.Encode
import Grass.ISA.X86.Target.Ledger
import Grass.ISA.X86.Target.Native
import Grass.ISA.X86.Target.State
import Grass.Memory.Access
import Grass.Memory.AddressSpace
import Grass.Memory.Addressing
import Grass.Memory.Apply
import Grass.Memory.Audit
import Grass.Memory.Authority
import Grass.Memory.Backing
import Grass.Memory.ByteStore
import Grass.Memory.Coordinates
import Grass.Memory.Event
import Grass.Memory.Fault
import Grass.Memory.GrantMint
import Grass.Memory.Loan
import Grass.Memory.LoanBatch
import Grass.Memory.Machine
import Grass.Memory.Ordering
import Grass.Memory.Profile
import Grass.Memory.Provenance
import Grass.Memory.Range
import Grass.Memory.Rights
import Grass.Memory.Shape
import Grass.Memory.SpatialAccess
import Grass.Memory.SpatialRange
import Grass.Memory.State
import Grass.Memory.StorageId
import Grass.Memory.Substep
import Grass.Memory.Synchronization
import Grass.Obligation.Core
import Grass.Obligation.Delta
import Grass.Obligation.Disposition
import Grass.Op.AccessFactory
import Grass.Op.AccessRun
import Grass.Op.CallProtocol
import Grass.Op.CallProtocolCustody
import Grass.Op.CallProtocolSettlement
import Grass.Op.CompletedAccess
import Grass.Op.Completion
import Grass.Op.Facets
import Grass.Op.PreparedPlacement
import Grass.Op.ReadBytes
import Grass.Op.ReadCompletion
import Grass.Op.ReadObservation
import Grass.Op.Step
import Grass.Op.WriteCompletion
import Grass.Platform.BareMetal.AArch64BootFetch
import Grass.Platform.BareMetal.BootFetch
import Grass.Platform.BareMetal.BootMemory
import Grass.Platform.BareMetal.Device
import Grass.Platform.BareMetal.Environment
import Grass.Platform.BareMetal.Registers
import Grass.Platform.BareMetal.Target
import Grass.Platform.BareMetal.Target.AArch64
import Grass.Platform.BareMetal.X86BootFetch
import Grass.Platform.Hosted.Clock
import Grass.Platform.Hosted.Console
import Grass.Platform.Hosted.Environment
import Grass.Platform.Hosted.Heap
import Grass.Platform.Hosted.Responds
import Grass.Platform.Linux.Syscall
import Grass.Platform.Linux.Target
import Grass.Platform.Linux.Target.AArch64
import Grass.Platform.Linux.Target.Errno
import Grass.Platform.Linux.Target.X86
import Grass.Platform.Linux.X86
import Grass.Platform.WASI.Target
import Grass.Platform.Win32.Target
import Grass.Platform.Win32.Target.Abi
import Grass.Platform.Win32.Target.Decode
import Grass.Platform.Win32.Target.Domain
import Grass.Platform.Win32.Target.Entry
import Grass.Platform.Win32.Target.Handles
import Grass.Platform.Win32.Target.ImportTable
import Grass.Platform.Win32.Target.Return
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
import Grass.Process.Function.ExecutionBounds
import Grass.Process.Function.Serial
import Grass.Process.Network.Assertion
import Grass.Process.Network.Channel
import Grass.Process.Network.Child
import Grass.Process.Network.Commit
import Grass.Process.Network.Death
import Grass.Process.Network.Delivery
import Grass.Process.Network.Escrow
import Grass.Process.Network.EscrowReceive
import Grass.Process.Network.Exposure
import Grass.Process.Network.Graph
import Grass.Process.Network.Initial
import Grass.Process.Network.Instance
import Grass.Process.Network.Mailbox
import Grass.Process.Network.Plan
import Grass.Process.Network.Progress
import Grass.Process.Network.Receive
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
import Grass.Refinement.Coverage
import Grass.Refinement.FiniteHistoryRelation
import Grass.Refinement.FinitePathMap
import Grass.Resource.Algebra
import Grass.Resource.Axis
import Grass.Semantics.Execution
import Grass.Semantics.History
import Grass.Semantics.InfiniteHistory
import Grass.Semantics.Observation
import Grass.Semantics.SpecProcess
import Grass.Service.Domain
import Grass.Shader.CompositeConnection
import Grass.Shader.SPIRV.Module
import Grass.Shader.SPIRV.Target
import Grass.Shader.WGSL.Composite
import Grass.Shader.WGSL.Module
import Grass.Shader.WGSL.Target
import Grass.Spec.Console
import Grass.Spec.Grammar
import Grass.Spec.Graphics
import Grass.Spec.Resource
import Grass.Spec.Root
import Grass.Specification.Boundary
import Grass.Specification.Scope
import Grass.Specification.TextLine
import Grass.Std.Logical.Byte
import Grass.Std.Logical.ByteOrder
import Grass.Std.Logical.FiniteMap
import Grass.Std.Logical.HostBytes
import Grass.Std.Logical.Order
import Grass.Std.Logical.StableSort
import Grass.Std.Logical.Text
import Grass.Std.Logical.Vec
import Grass.Std.Sort.Descriptors
import Grass.Std.Sort.Stable
import Grass.Std.Zlib.CRC32
import Grass.Std.Zlib.Deflate.Core
import Grass.Std.Zlib.Deflate.Equivalence
import Grass.Std.Zlib.Deflate.FixedBlockBridge
import Grass.Std.Zlib.Deflate.FixedSizeBound
import Grass.Std.Zlib.Deflate.Huffman
import Grass.Std.Zlib.Deflate.SizeBound
import Grass.Std.Zlib.Fixed32K
import Grass.Std.Zlib.Fixed32K.Checksum
import Grass.Std.Zlib.Gzip.Header
import Grass.Std.Zlib.Gzip.Member
import Grass.Std.Zlib.Gzip.SizeBound
import Grass.Std.Zlib.Gzip.Trailer
import Grass.Std.Zlib.Support
import Grass.Target.Artifact
import Grass.Target.Checkpoint
import Grass.Target.Device
import Grass.Target.ISA
import Grass.Target.Machine
import Grass.Target.Platform
import Grass.Target.Raw
import Grass.Target.Safety
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
