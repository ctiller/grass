# Protocol standard-library candidate

Status: candidate interface for implementation. This document does not claim
that the Lean library, generators, or certificates exist.

## Purpose

Application specifications should select a protocol profile and state their
application behavior. They should not manually reconstruct the protocol's frame
grammar, parser-process requirements, error matrix, partial-I/O adapters,
resource axes, cancellation rules, citation ledger, or standard model proofs.

Protocol semantics remain precious. The package removes plumbing, not meaning.
Selecting HTTP/2 commits the root `SpecProcess` to the accepted/rejected wire
language and RFC behavior exported by that exact profile. Parser topology,
buffer layout, scheduling, platform APIs, and assembly remain replaceable.

## Package shape

```lean
structure ProtocolShape (R : Type u) [ResourceModel R] where
  Role : Type
  State : Role -> Type
  Input : Role -> Type
  Output : Role -> Type
  Error : Role -> Type
  Command : Role -> Type
  wireFormats : FiniteKeyedFormatFamily
  initial : (role : Role) -> State role
  transition : State role -> Input role ->
    ProtocolStep (State role) (Output role) (Command role) (Error role)
  observations : ProtocolObservationProjection
  resources : ProtocolResourceSemantics R
  obligations : ProtocolObligationSemantics
  progress : ProtocolProgressSemantics
  errorTotal : EveryRejectedEventHasExactlyOneTypedScopeAndCode
  transitionTotal : EveryStateInputHasExactlyOneStepOrTypedError
```

The transition system is logical. It does not decide whether roles become
threads, callbacks, processes, serial functions, basic blocks, or inlined
assembly. A package may expose useful process presentations, but the root
denotation is independent of those presentations.

```lean
structure ProtocolPackage (R : Type u) [ResourceModel R] where
  shape : ProtocolShape R
  requirements : FiniteKeyedProcessDemandFamily R
  requirementOrigin :
    requirements = ProtocolRequirements.capture shape.wireFormats
      shape.transition shape.resources shape.obligations shape.progress
  specProcess : SpecProcess R
  captureExact : specProcess.requirements = requirements
  modelCorrect : ProtocolModelSatisfies specProcess shape
  citations : ProtocolCitationLedger shape
  mutations : ProtocolMutationSchema shape
```

`requirements` includes “a process implementing this parser/writer” demands for
each selected wire format. It does not contain a selected parser implementation.
It also includes protocol transition, error, resource, obligation, and progress
demands. It does not contain WinSock, Win64, x86, PE, or requirement-closure
facts; those arise in later obligation families.

## Profile selection

A protocol family owns versioned profiles. A profile selects semantics, not a
physical implementation:

```lean
structure Http2.ServerProfile (R : Type u) [ResourceModel R] where
  transport : Http2.Transport
  semanticBudget : Http2ServerSemanticBudget
  requestPolicy : Http2.RequestPolicy
  responsePolicy : Http2.ResponsePolicy
  extensionPolicy : Http2.ExtensionPolicy
  progressPolicy : Http2.ProgressPolicy
  rfc : Http2.RfcProfile := .rfc9113
  hpack : Hpack.RfcProfile := .rfc7541

def Http2.Server.package
    (resources : R)
    (profile : Http2.ServerProfile R)
    (routes : Http2Routes) : ProtocolPackage R
```

The package derives frame and HPACK formats, parser/writer process demands,
connection/stream state machines, mandatory pseudo-header rules,
`content-length` conservation, SETTINGS directionality, flow control, scoped
errors, unknown-extension stuttering, cancellation frontiers, and resource
axes. The application does not pass these individually.

The selected profile is retained as data in the root specification. A profile
change therefore changes the captured requirements and invalidates the first
adjacent witness. There is no ambient registry or typeclass search after
capture.

## Author surface

The HTTP/2 server spike should be approximately:

```lean
import Grass.Std.Protocol.Http2

def profile : Http2.ServerProfile resources :=
  Http2.ServerProfile.rfc9113CleartextPriorKnowledge
    (budget := semanticBudget)
    (push := .disabled)
    (priority := .ignoreDeprecatedSignals)
    (requestBodies := .discardWithinFlowControl)

def protocol : ProtocolPackage resources :=
  Http2.Server.package resources profile routes

def spec : SpecProcess resources :=
  protocol.specProcess.withProgress serverProgress
```

Routes and any application-specific behavior theorem remain authored. Frame and
HPACK parser requirements, their round-trip laws, and standard protocol model
correctness are fields of `protocol` and appear in the generated obligation
report, not as proxy declarations in the spike.

## Implementations and staged obligations

One portable requirement family cannot contain target-specific obligations.
Protocol lowering uses five disjoint, keyed stages:

```lean
inductive ProtocolProofStage
  | portable | projection | provider | machine | artifact

structure StagedProtocolObligations (package : ProtocolPackage R) where
  portable : DemandFamily := package.specProcess.requirements
  projection : DerivedDemandFamily portable
  provider : DerivedDemandFamily projection
  machine : DerivedDemandFamily provider
  artifact : DerivedDemandFamily machine
  origin : EveryDerivedDemandHasOnePriorStageOrigin
  disjoint : PairwiseDisjointKeys portable projection provider machine artifact
```

Requirement closure is a meta-theorem over the disjoint union. It is not itself
a member of any family. Adding or moving a demand makes the first wrong stage
ill-typed. Review inventories such as `HTTP2_CONSTRAINTS.md` are generated
projections from this staged value, not parallel authority.

A protocol implementation chooses witnesses:

```lean
structure ProtocolRealization
    (package : ProtocolPackage R)
    (plan : PlatformPlan package.specProcess.driverBoundary.requirements) where
  selectedProcesses : SelectedProcessWitnessFamily package.requirements
  substitutionExact : OccurrenceExactRequirementSubstitution
    package.specProcess selectedProcesses
  presentation : ProcessPresentation package.specProcess
  presentationExact : presentation.denotation = package.specProcess.denotation
```

Parser implementations may be serial functions, generated tables, process
graphs, or custom assembly. A standard implementation supplies its
representation and local simulation once. Custom assembly remains first class
and can replace any selected component by proving the same keyed demand.

## Partial I/O and asynchrony

Every wire protocol consumes and produces `Std.Process.ByteFlow` channels.
Positive reads yield ordered nonempty chunks; EOF, pending, cancellation, and
failure are distinct. Parsing is invariant under all chunkings of the same byte
stream. Positive writes commit exact prefixes and retain unique ownership of the
suffix. This interface is shared by blocking calls, readiness polling, IOCP,
`io_uring`, pipes, files, and in-memory channels.

The package therefore never bakes `recv`, `WSAPoll`, or IOCP into the protocol.
A staged provider replacement proves the same byte-channel, custody, progress,
and cancellation boundary and composes by process-refinement congruence.

## Error matrices

Protocols with scoped errors export a generated exhaustive matrix:

```lean
structure ProtocolErrorMatrix (shape : ProtocolShape R) where
  classify : (state : shape.State role) -> (input : shape.Input role) ->
    Except (shape.Error role) (ProtocolStep ...)
  exact : classify = shape.transition
  coverage : EveryInvalidCaseAppearsExactlyOnce classify
  scopeAndCodeExact : EveryErrorHasSpecificationMandatedScopeAndCode classify
```

Normalizers return typed errors. They do not jump to an undifferentiated shared
failure edge. A mutation which changes one code, scope, or accepted case must
fail at the matrix before machine proof.

## Composition and gRPC

Protocol packages compose by typed boundary refinement. gRPC is an extension of
HTTP/2, not a copied transport model:

```lean
def Grpc.Server.package
    (http2 : Http2.Server.Package R)
    (services : Grpc.ServiceRegistry)
    (profile : Grpc.ServerProfile R) : ProtocolPackage R

theorem Grpc.Server.restrictsToHttp2 :
  RestrictRequirements grpc.specProcess `h2 =
    http2.specProcess.requirements
```

The gRPC package adds message deframing, compression flags/codecs, metadata and
trailers, method/RPC state machines, deadlines/status mapping, application
obligations, and message/resource bounds. It reuses HTTP/2 stream identity,
flow control, partial I/O, HPACK, error scoping, cancellation, and artifact
closure. Nested protocols may be flattened into one serial process where a
`SerializablePlan` exists or realized as a process graph otherwise.

## Proposed module surface

```text
Grass.Std.Protocol.Core
Grass.Std.Protocol.ByteFlow
Grass.Std.Protocol.Grammar
Grass.Std.Protocol.Errors
Grass.Std.Protocol.Resources
Grass.Std.Protocol.Realization
Grass.Std.Protocol.Http2
Grass.Std.Protocol.Http2.X86
Grass.Std.Protocol.Grpc
```

The umbrella module exports the concise application surface. Internal modules
remain separately checkable and carry stable verified-object summaries so an
HPACK, frame, gRPC-message, provider, or assembly edit does not reopen unrelated
protocol siblings.

## Implementation ratchet

Before this candidate becomes normative library API, one command must emit:

- the captured portable demand family and exact origin keys;
- each later staged obligation family and its prior-stage origin;
- selected parser/writer/process witnesses;
- the complete error matrix and negative fixtures;
- partial-read/write partition fixtures;
- resource/cancellation summaries;
- local assembly scopes, representation relations, and residual goals; and
- shard identities, dependency edges, clean/incremental work, proof size, and
  peak memory.

HTTP/2 acceptance must cover every RFC-profile row in
[HTTP2_CONSTRAINTS.md](HTTP2_CONSTRAINTS.md). The later gRPC package extends the
same report rather than starting a second checklist.
