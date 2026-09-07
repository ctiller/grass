import Lean
-- `Tests` as well as `Grass`, because a fixture is enforcement.
--
-- `Tools/DocstringAudit.py` asks whether a claim names something a reader can
-- chase, and §3.10's rule is "name the enforcing type or theorem". In the memory
-- layer the enforcement of a refusal is routinely a *fixture* -- the docstrings
-- there cite `the_identity_cannot_be_stolen` and its siblings the way the ISA
-- docstrings cite lemmas -- so a name set built from `Grass/` alone reported three
-- true citations as naming nothing. `Tools/CitationAudit.py` already adjudicates
-- those names and resolves them, which is how the disagreement surfaced.
--
-- This widens what the docstring audit will accept as enforcement, and the
-- coverage guard below covers **both** trees: a missing `Tests` module shrinks the
-- name set exactly as a missing `Grass` one does, and this comment said the guard
-- stayed scoped to `Grass/` while the code four lines down already filtered both.
-- **Six** `Tests` modules are deliberately absent: each defines a `main`, and two
-- `main`s cannot share one environment. They are corpus generators and machine
-- probes -- programs that *produce* evidence rather than declarations a docstring
-- would cite as enforcement -- so excluding them costs the name set nothing. The
-- guard below lists them by name rather than pattern, so a new one is a loud
-- failure and a decision rather than a silent omission.
--
-- This said seven and the list held eight, and two of the eight suppressed
-- nothing. `Tests` itself can never appear in the enumeration, which only
-- produces `Tests.X` names. And `Tests.Memory.Spike1Reference` defines no `main`
-- at all -- the grep that put it here matched `mainThread` -- is not a generator
-- or a probe but this layer's M1 freeze evidence, and was in the name set anyway,
-- transitively, through two modules that import it. Both are gone. An exclusion
-- list written by grepping for a keyword is a list of what the grep matched.
import Tests.Foundation
import Tests.ISA.X86.CorpusCommon
import Tests.ISA.X86.LedgerAudit
import Tests.ISA.X86.Spike1Addressing
import Tests.Memory.AtomicAuthority
import Tests.Memory.EventClauses
import Tests.Memory.Loans
import Tests.Memory.Padding
import Tests.Memory.Placement
import Tests.Memory.RiskOneCases
import Tests.Memory.Spike1Block
import Tests.Memory.Spike1Policy
import Tests.Memory.StraightLineBlock
import Tests.Memory.WellFormedClauses
import Tests.Op.FakeIsa
import Tests.Op.StandardLoan
import Tests.Process.AdapterFixtures
import Tests.Process.AssertionFixtures
import Tests.Process.BlendFixtures
import Tests.Process.CancellationFixtures
import Tests.Process.ChannelFixtures
import Tests.Process.ChannelStepFixtures
import Tests.Process.ChatterFixtures
import Tests.Process.ChildBindingFixtures
import Tests.Process.CloseFixtures
import Tests.Process.CommitFixtures
import Tests.Process.ComposeFixtures
import Tests.Process.CountdownCorrectFixtures
import Tests.Process.DeliveryFixtures
import Tests.Process.DetachFixtures
import Tests.Process.EndingFixtures
import Tests.Process.EscrowFixtures
import Tests.Process.FacadeCancellationFixtures
import Tests.Process.FacadeFixtures
import Tests.Process.FacetFixtures
import Tests.Process.FrontierFixtures
import Tests.Process.IndependenceFixtures
import Tests.Process.InstanceFixtures
import Tests.Process.LayeringFixtures
import Tests.Process.LayeringSpecificationOnly
import Tests.Process.LensFixtures
import Tests.Process.LifecycleStepFixtures
import Tests.Process.LinearizationFixtures
import Tests.Process.M1CorrectFixtures
import Tests.Process.M1Fixtures
import Tests.Process.M2GraphFixtures
import Tests.Process.MailboxFixtures
import Tests.Process.OscillateFixtures
import Tests.Process.PrefixFixtures
import Tests.Process.PreservationFixtures
import Tests.Process.ProcessStepFixtures
import Tests.Process.ProgressFixtures
import Tests.Process.RerouteFixtures
import Tests.Process.RestartFixtures
import Tests.Process.RichAcceptanceFixtures
import Tests.Process.SequentialEffectFixtures
import Tests.Process.SerialFixtures
import Tests.Process.SpinFixtures
import Tests.Process.StandardFixtures
import Tests.Process.StructuralNetworkFixtures
import Tests.Process.TerminationFixtures
import Tests.Process.TransitionFixtures
import Tests.Process.ViewFixtures
import Tests.Process.WeaveFixtures
import Tests.Process.WorldFixtures
import Tests.Resource.CompositionSplit
import Tests.Std.Chunking
import Tests.Std.HostBytes
import Tests.Std.PartialWrite
import Tests.Std.SpikeSurface
import Tests.Std.StableSort
import Tests.Std.Text
import Tests.Std.VecInstances
import Tests.Std.VecVocabulary
import Grass.Core.Context
import Grass.Core.Demand
import Grass.Core.Generational
import Grass.Core.Identifiers
import Grass.Core.Name
import Grass.Core.Uid
import Grass.ABI.Win64.Convention
import Grass.ABI.Win64.Unwind
import Grass.ABI.Win64.UnwindBytes
import Grass.Certificate
import Grass.ISA.X86.Addressing
import Grass.ISA.X86.Bytes
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
import Grass.Memory.Addressing
import Grass.Memory.Apply
import Grass.Memory.ByteStore
import Grass.Memory.Loan
import Grass.Memory.Shape
import Grass.Memory.AddressSpace
import Grass.Memory.Audit
import Grass.Memory.Authority
import Grass.Memory.Event
import Grass.Memory.Fault
import Grass.Memory.Ordering
import Grass.Memory.Profile
import Grass.Memory.Provenance
import Grass.Memory.Range
import Grass.Memory.Rights
import Grass.Memory.State
import Grass.Memory.Substep
import Grass.Obligation.Core
import Grass.Obligation.Delta
import Grass.Obligation.Disposition
import Grass.Op.Facets
import Grass.Platform.Win32.Console
import Grass.Op.Step
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
import Grass.Resource.Algebra
import Grass.Resource.Axis
import Grass.Semantics.Execution
import Grass.Semantics.Observation
import Grass.Semantics.SpecProcess
import Grass.Specification.Boundary
import Grass.Specification.Scope
import Grass.Std.Logical.Bag
import Grass.Std.Logical.Byte
import Grass.Std.Logical.FiniteMap
import Grass.Std.Logical.HostBytes
import Grass.Std.Logical.Order
import Grass.Std.Logical.Text
import Grass.Std.Logical.Vec
import Grass.Trust.Audit
import Grass.Verify.VerifiedProgram

/-!
# Every declaration name the build knows

`Tools/DocstringAudit.py` requires a strong claim in a docstring to name the type
or theorem that enforces it. It checked that the sentence contained *a backticked
identifier* and nothing more, so an invented name satisfied it — a reviewer
passed the audit with a sentence naming
`encodeMem_is_canonical_and_injective_over_all_addresses`, which does not exist
and never did. That is the exact defect the tool's own header says it was built
for: `.github/workflows/library.yml` records "one naming a theorem that did not
exist".

The tool cannot be given a Lean environment, so this prints one for it. Every
constant name in the environment, one per line, with `private` mangling stripped
so a docstring can name a private theorem by the name it is written under.

Not restricted to `Grass`: docstrings legitimately name core declarations —
`BitVec`, `List.find?`, `Option.isSome` — and a checker that rejected those would
push authors towards naming nothing rather than towards naming something real.

This is not a proof and not an audit. It is a fact dump, and the tool that reads
it still cannot tell whether the named theorem proves the sentence. It closes one
gap: whether the name resolves at all.
-/

open Lean

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

run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  -- The same coverage guard `Tools/AxiomAudit.lean` carries, for the same
  -- reason: a module missing from this list would silently shrink the name set,
  -- and every docstring naming one of its declarations would be reported as
  -- naming nothing. A loud failure beats a mystery finding.
  let imported := env.header.moduleNames
  let onDisk ← modulesOnDisk (System.FilePath.mk "Grass") `Grass
  let onDiskTests ← modulesOnDisk (System.FilePath.mk "Tests") `Tests
  -- The six modules above, and only those. `Tests` is not enumerated by
  -- `modulesOnDisk` and `Tests.Memory.Spike1Reference` has no `main`; both were
  -- here and both suppressed nothing.
  let generators : Array Name :=
    #[`Tests.ABI.Win64.UnwindCorpus, `Tests.ISA.X86.DecodeCorpus,
      `Tests.ISA.X86.MachineProbes, `Tests.ISA.X86.NasmCorpus,
      `Tests.ISA.X86.RipCorpus, `Tests.ISA.X86.SourceCorpus]
  let missing := (onDisk ++ onDiskTests.filter (fun m => !generators.contains m)).filter
    fun m => !imported.contains m
  unless missing.isEmpty do
    throwError m!"declaration list coverage gap: these modules exist under Grass/ or Tests/ but are not imported by Tools/DeclNames.lean:
{MessageData.joinSep (missing.toList.map (m!"  {·}")) "
"}"
  let mut out : Array String := #[]
  for (name, _) in env.constants.toList do
    let user := (privateToUserName? name).getD name
    unless user.isInternal do
      out := out.push user.toString
  for line in out do
    IO.println line
