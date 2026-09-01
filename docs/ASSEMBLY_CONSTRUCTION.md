# Typed assembly construction and layout

Grass treats Lean as a general program-construction language. First-class
assembly means the authored and reviewed result is an exact instruction stream;
it does not require authors to calculate every offset, prologue, spill, or short
instruction sequence by hand. This document owns typed layout definitions,
instruction-fragment generators, and their proof boundary.

## 1. Authoring model: Lean construction, assembly surface

Grass does not adopt a textual macro preprocessor as its semantic construction
language. The primary abstraction is a total Lean function from typed inputs to
an `AsmFragment` or `VerifiedFragment`. Assembly quotation is the concise
surface language for literal instructions and may splice those values:

```lean
def writeCall (handle src : Gpr64) (count : Gpr32) :=
  withStack (transferred : UInt32 := 0)
  withCallFrame WriteFile asm {
    mov rcx, handle
    mov rdx, src
    mov r8d, count
    lea r9, transferred.addr
    arg WriteFile.overlapped, 0
    call qword ptr [rip + __imp_WriteFile]
  }
```

This is intentionally two views of one artifact, not two classes of assembly.
An author may write every instruction literally, use library constructors, or
mix the two instruction by instruction. Every splice expands to a finite raw
instruction sequence before source closure and verification.

`withCallFrame` derives shadow space and named stack arguments from the selected
cited ABI/API signature. It does not hide the call, register arguments, possible
outcomes, or obligations; the expanded view shows its concrete stack operands.

Mature assemblers establish useful authoring expectations:

- NASM's macros supply named, default, required, and variadic parameters,
  hygienic macro-local labels, repetition, conditional construction, context
  stacks, structure offsets, initialized structure instances, and an expanded
  preprocessing view.
- MASM's `STRUCT`, `RECORD`, and procedure-local declarations demonstrate the
  value of named aggregate fields, bitfield definitions, and scoped storage.
- GNU `as` couples procedure instructions to CFI directives, demonstrating why
  prologue construction and unwind facts must come from the same description.

Grass should match those conveniences with typed Lean values. It should not
inherit token-substitution order, stringly operands, ambient preprocessor state,
or implicit prologue magic. Fresh labels are unforgeable scoped identifiers;
parameters have operand classes; repetition is an ordinary function over a
finite collection; alternatives return the same declared fragment contract.

Two construction tiers share the same result type:

1. pure, total Lean functions and indexed builder combinators are the preferred
   reusable mechanism;
2. elaborator syntax may remove punctuation and infer operands, but must expose
   its generated Lean term and expanded instruction list.

The review interface always offers authored, elaborated, and expanded views.
The last view is the exact input to ghost erasure and encoding.

### 1.1 Constructors are theorem families

A fragment constructor is a proof abstraction, not only a source abbreviation.
It should state the strongest economical parametric theorem about every sequence
it can generate:

```lean
def saveNonvolatile
    (frame : StackLayout abi) (regs : Vec (Nonvolatile abi) n)
    (fits : frame.HasSlotsFor regs) :
    VerifiedFragment
      (SaveEntry abi frame regs)
      (SaveExit abi frame regs) := ...

theorem saveNonvolatile_expansion
    (frame) (regs) (fits) :
    (saveNonvolatile frame regs fits).expanded =
      regs.mapWithIndex (fun i reg => mov frame.slot[i], reg) := ...
```

The returned certificate may cover exact expansion, local Hoare behavior,
memory accesses, faults, stack delta, preserved state, obligations, resource
change, cancellation interaction, unwind metadata, and citation coverage. It
must expose rather than silently weaken any dimension on which callers rely.

At a use site Grass checks typed arguments and composes the fragment's entry and
exit contracts. It does not re-derive the per-instruction proof. Encoding still
expands the sequence, and an adversarial review may request that expanded form,
but proof checking can retain a hierarchical reference to the already checked
constructor theorem plus its small instantiation witness. This is a principal
scalability mechanism for both proof size and incremental builds.

The invalidation boundary is deliberate: changing a constructor's theorem or
expansion rechecks that constructor and its dependent instantiations; changing
an unrelated caller does not reopen the constructor proof. A literal sequence
may be promoted into such a family after its useful parameters and strongest
stable contract are identified. Novel one-off assembly never has to be forced
through a constructor first.

## 2. Construction is not proof authority

Lean functions and metaprograms may compute layouts, choose encodings, allocate
temporary registers, generate tables, and emit arbitrary finite instruction
fragments. The generator is not trusted merely because it ran. Its result must
arrive with one of:

- a theorem constructed from verified combinators;
- a compact certificate checked by a kernel-proved checker; or
- explicit residual proof goals discharged by the author.

The closed source records the exact generated fragment and generator inputs.
Ghost erasure and raw emission see only ordinary target instructions. Re-running
a generator is construction; it never substitutes for a forall theorem about
the resulting instructions.

Closed source is hierarchical. Each literal fragment, constructor instance,
macro expansion, and static-data fragment has its own exact expansion,
symbol/import summary, and local machine certificate. Shards compose those
exports with an exact interface-matching theorem; components compose shard
summaries in the same way. The final raw listing is obtained by induction over
that tree and can be streamed to the writer. No whole-program boolean scan or
`decide` over a flattened instruction array is accepted as the routine closure
proof for a large program.

This does not weaken exactness: the root still proves that every authored
fragment appears exactly once, every reference resolves, every macro expansion
is the selected one, and the recursively concatenated listing is precisely the
writer input. It changes the proof's ownership and invalidation boundary. A
leaf mutation rechecks the leaf and ancestor interfaces; unchanged sibling
certificates remain ordinary imported kernel-checked theorems.

The author does not maintain a parallel symbol array, block-name dictionary,
stack-object ledger, constructor-name table, or cancellation lookup map. The
assembly elaborator derives those values structurally from the same typed AST
which produces the expanded source. Block attributes such as `@placement`,
`@invariant`, `@cancellation_point`, and safe-state classifications elaborate
typed terms and become fields of the block node. Closure and total CFG
classification are folds over that AST; renaming or splitting a block changes
the source and derived manifest atomically.

Generated manifests and expanded listings may be committed outside the
author-maintained spike directory or embedded in the annotated spike document,
but they are checked projections, never a second author-maintained source of
truth. A custom source frontend must prove that its extracted manifest equals
the core AST projection before it can enter hierarchical closure.

Every nonlocal input to source elaboration is a dependent field of the authored
source term, never an ambient namespace scan or global registry lookup:

```lean
structure AuthoredSourceInputs (plan : PlatformPlan requirements) where
  statics : StaticObjectTable
  constructors : FragmentConstructorClosure plan
  layouts : LayoutSelection plan
  requirementWitnesses : RequirementSubstitution plan.spec

def source : AsmSource plan :=
  asm_source
    (statics := selectedStatics)
    (constructors := selectedConstructors)
    (layouts := selectedLayouts)
    (requirements := selectedRequirementWitnesses) {
      -- literal instructions and typed constructor applications
    }
```

The syntax may omit an empty or uniquely derivable field, but elaboration prints
the inferred term and proves uniqueness. Referencing a symbol, constructor,
layout path, or required child process not reachable from these dependent inputs
is a source-closure error. Thus edits to static data, constructors, layouts, and
selected child processes change source identity at the first adjacent boundary.

### 2.1 Staged assembly checking

`verify_asm` is an orchestrator over separately callable checked phases:

1. `asm_elaborate` resolves typed operands, labels, constructors, layouts, ABI
   call frames, and derived manifests;
2. `asm_symbolic` performs deterministic instruction/CFG symbolic execution and
   emits local verification conditions;
3. `asm_frame` normalizes spatial ownership, provenance, loans, access
   footprints, and framed resource assertions;
4. `asm_arith` dispatches Presburger and bit-vector goals to kernel-checked
   procedures such as `omega` and `bv_decide`;
5. `asm_ghost` checks obligation, custody, cancellation, resource-flux, and
   observation transitions; and
6. `asm_close` composes block/fragment certificates and reports every residual
   theorem demand.

No phase performs open-ended search across another phase's domain. Each may be
run independently and every failure identifies the instruction, CFG edge,
logical contract, and residual proposition. Reflection can make proof terms
compact, but its evaluation cost is measured rather than mislabeled constant.

Every invocation returns an auditable report in addition to its certificate:

```lean
structure AssemblyCheckReport (source : AuthoredAsmSource) where
  expandedSource : RawInstructionHierarchy
  consumedContracts : FiniteContractManifest source
  consumedCitations : InstructionAnchorManifest expandedSource
  phaseResults : FiniteMap AssemblyCheckPhase PhaseResult
  residualGoals : Array ResidualGoal
  residualAllowlist : Array ResidualGoalKey
  allowlistExact : residualGoals.map ResidualGoal.key = residualAllowlist
  elapsedByPhase : FiniteMap AssemblyCheckPhase Duration
  proofTermBytesByShard : FiniteMap SourceShard Nat
```

`verify_asm` succeeds only when every residual is discharged explicitly or is
present in the reviewed source-local allowlist. A missing block invariant, an
unhandled provider result, and an absent semantic correspondence are mutation
fixtures which must remain as residual goals in respectively `asm_symbolic`,
`asm_ghost`, and `asm_close`; no later phase may silently solve or reclassify
them.

## 3. Object and aggregate layout

Logical objects and physical layout remain separate:

```lean
structure FieldSpec where
  name : Name
  Value : Type
  repr : ObjectRepr profile Value

structure StructLayout (profile : LayoutProfile) (fields : List FieldSpec) where
  uniqueNames : fields.Pairwise (fun left right => left.name != right.name)
  offset : (field : fields.Member) -> Nat
  size alignment : Nat
  aligned : EveryFieldAligned fields offset
  disjoint : LiveFieldByteRangesDisjoint fields offset
  contained : EveryFieldEndsAtOrBeforeSize fields offset size
  aggregateAligned : alignment ∣ size

def StructLayout.lookup (layout : StructLayout profile fields)
    (name : Name) : Option (Sigma fun field : fields.Member =>
      field.value.name = name)

theorem StructLayout.lookup_exact (layout : StructLayout profile fields) :
  layout.lookup name = some field iff field.value.name = name

def playerLayout := structLayout win64 {
  position : Vec3f
  health : UInt32
  flags : BitVec 16
}
```

`layout.field.offset`, `layout.size`, and `layout.alignment` compute to concrete
natural numbers. Access helpers carry the field representation, initialization,
permission, provenance, and range theorem. Named layout does not imply the C ABI;
a `CLayout profile`, `Win64AbiLayout`, packed layout, device layout, or wire
format is an explicit selected profile with cited rules. Unions, tagged unions,
base classes, flexible tails, zero-sized objects, bitfields, and padding have
separate constructors and proof obligations rather than accidental C guesses.

Arrays derive stride and checked index arithmetic. Nested layouts compose offset
proofs. A layout may generate reader/writer code, but serialization still uses
the independent grammar laws in [GRAMMAR.md](GRAMMAR.md).

## 4. Stack frames and call bursts

A stack layout specializes aggregate layout with ABI and unwind laws:

```lean
def frame := stackLayout win64 {
  written : UInt32
  overlapped : UInt64
  savedStatus : UInt32
}

def body := asm {
  enter frame (save := [rbx, r12, r13])
  store frame.written, 0
  lea r9, frame.addr .written
  withCallFrame win64 WriteFile
  leave frame
}
```

`enter`, `leave`, `save`, `restore`, `spill`, `reload`, `withCallFrame`, and
typed slot operations are transparent fragment generators. For Win64 they prove
the selected stack alignment, shadow space, nonvolatile preservation, balanced
stack delta, initialized-slot use, and exact correspondence between prologue
instructions and generated `UNWIND_INFO`. A prologue outside the representable
unwind subset remains authorable but must provide its own legal unwind/leaf
profile theorem.

Short bursts are ordinary values:

```lean
structure FragmentExitFamily (entry : BlockContract) where
  Kind : Type
  contract : Kind -> BlockContract
  normal : Option Kind
  classifies : forall exit : FragmentMachineExit,
    ExactlyOneKindClassifiesExit entry contract exit
  complete : EveryNormalFaultCancellationInterruptionAndUnwindExitCovered
    entry contract

structure VerifiedFragment
    (entry : BlockContract) (exits : FragmentExitFamily entry) where
  source : GhostInstructionList
  expanded : RawInstructionList
  expansionExact : ErasesExactly source expanded
  localCorrect : HoareSequenceAllExits entry expanded exits
  citations : InstructionAnchorCoverage expanded
```

A generator can be Turing complete while every returned fragment remains finite,
exact, and locally checked. Recursive generation must terminate as Lean
construction; generated machine loops are verified through CFG loop contracts,
not Lean recursion.

### 4.1 Lexical stack objects

Routine assembly should be able to request typed addressable objects without
hand-authoring a monolithic frame declaration:

```lean
def copyFields :=
  withStack (x : TypeA := .uninitialized)
            (y : TypeB := initialY) asm {
    $(copy x.a y.k)
  }
```

On x86 two stack fields cannot be operands of one `mov`. `copy` is visibly a
verified short-burst constructor and may select a legal temporary. An author
who wants the precise instruction choice writes it directly:

```lean
withScratch tmp asm {
  mov tmp, y.k
  mov x.a, tmp
}
```

`withStack` is an elaboration and lifetime binder. `x` and `y` are
`StackObject TypeA` and `StackObject TypeB`; field projection produces typed
memory operands carrying width, alignment, provenance, permission, and current
initialization facts. The displayed `copy` requires `y.k` initialized and
readable, requires `x.a` writable, and establishes initialization of `x.a`.
Incompatible field representations fail locally.

The binder itself need not emit an instruction. It contributes object demands
to the enclosing frame planner, which may pack and reuse storage whose lexical
lifetimes do not overlap. The one reviewed frame plan determines prologue size,
unwind metadata, and the raw `[rsp+offset]` operands shown in the expanded view.
Nested binders compose; branch joins reconcile initialization and outstanding
loans. Distinct bindings are disjoint unless an explicit union/overlay
constructor proves a shared representation.

Useful surface variants include:

```lean
withStack (x : TypeA := .uninitialized)
          (y : TypeB := initialY) asm { ... }

withStackAt pinnedFrame (x : TypeA := slotA) asm { ... }
```

An uninitialized binding emits no clearing store. A supplied initializer is a
transparent verified fragment whose exact stores are visible. Scope exit proves
that no pointer, borrow, live return value, or obligation outlives its call-tied
stack provenance. Code that deliberately passes a stack pointer to a longer-
lived process must instead use an enclosing frame lifetime or another ownership
class and prove the transfer legal.

The binder releases storage provenance; it does not silently finalize a value
or adopt obligations stored inside it. Every CFG edge leaving the scope proves
the value trivially disposable, invokes an explicit verified finalizer, or
transfers those obligations to a longer-lived owner. Jumps into a scope are
rejected because they cannot construct its fresh provenance.

The constructor is a scope eliminator, not a textual macro:

```lean
def withStack
    (layout : StackObjectLayout alpha)
    (body : (fresh : StackProvenance) ->
      VerifiedFragment (entry.withStackObject fresh layout)
        (bodyExits fresh))
    (closes : forall fresh kind,
      ExitEliminatesFreshStackProvenance
        fresh ((body fresh).localCorrect.exit kind)) :
    VerifiedFragment entry (eliminateStackScope bodyExits closes)
```

Because `fresh` is locally quantified, the result type cannot mention it.
`closes` covers normal, fault, cancellation, interruption, explicit jump, and
unwind exits.  Standard disposable values discharge it automatically; values
with loans or obligations require a finalizer or an explicit transfer to an
outer owner.  The acceptance fixtures include successful nested use and
rejections for an escaping address, jump into scope, live borrow, missing fault
finalization, cancellation while owned, and a dynamic allocation exceeding its
proved bound.
forbidden, and jumps out are checked against the same exit contract as lexical
fallthrough.

The basic binder requires statically sized layouts. A separate bounded dynamic
form takes a proved maximum, checks size arithmetic, models the selected
platform's stack growth/probing and overflow outcome, and proves restoration on
every exit. Unbounded or silently probed dynamic stack allocation is not an
ordinary `withStack` convenience.

Authors retain complete physical control: they may constrain alignment,
relative order, reuse, fixed offsets, or the whole frame; disable reuse for
debuggability; or use literal `rsp` arithmetic with direct proofs. A named-layout
edit moves named uses automatically, while a pinned or literal displacement
fails at its local assertion rather than silently changing meaning.

## 5. Logical contracts and physical placement

Routine block invariants should not pin mathematical values to registers:

```lean
structure WriteLoopLogicalState where
  message : ByteArray
  committed remaining : Nat
  partition : committed + remaining = message.size

structure Placement (logical : Type) (machine : MachineShape) where
  locate : LogicalField logical -> MachineLocation machine
  represents : LocationsRepresentLogicalFields locate
  compatible : LocationsPairwiseCompatible locate

def writeLoopEntry (placement : Placement WriteLoopLogicalState shape) :
    BlockContract := ...
```

The assembly author may choose `ptr` in `r13`, spill it to a named stack slot,
or use another register and prove/update only the placement. A hand-tuned block
may instead state a deliberately physical contract when register identity,
flags, alignment, or instruction scheduling is part of its interface. Grass
does not force an allocator between the author and the assembly.

Assembly annotations elaborate Lean terms. `@invariant Foo.bar args` is not a
string label: `Foo.bar args` must have the invariant type expected at that CFG
point. Labels are Lean identifiers. Unknown predicates, wrong arguments, or a
contract referring to an unavailable placement fail elaboration before
verification.

## 6. Spike syntax and the raw escape hatch

The spikes are copied examples and therefore obey a stronger authoring rule
than the minimum accepted by Grass:

- fields, stack slots, static objects, ABI homes, and bitfields use named typed
  paths derived from layouts;
- calls use a transparent ABI burst when it removes bookkeeping without hiding
  the call, arguments, possible outcomes, or obligations;
- repeated straight-line idioms use a verified fragment constructor;
- numeric displacement appears only when the number is intrinsically part of
  the algorithm, an external format mandates the exact number, or the fixture
  is explicitly demonstrating the raw escape hatch;
- registers remain author-selected, but routine contracts state logical facts
  plus a placement instead of repeating register assignments as mathematics.

Thus `[state + GzipArena.crc]` is the exemplar spelling even though its expanded
x86 operand is `[r12+48]`. An indexed array access such as
`[records + index * LineRecord.stride]` remains recognizably assembly. A literal
`[r12+48]` is legal, but must carry or inherit the proof that it denotes the
intended field. Dedicated adversarial fixtures exercise that route; ordinary
spikes do not normalize it.

This rule is normative for maintained Grass examples, not a restriction on
program authors. Concision is measured in the authored view; exactness and
machine control are judged in the expanded view.

## 7. Generated versus literal assembly

Generated fragments and literal instructions are peers:

- any verified fragment may be expanded and locally edited as literal assembly;
- a literal sequence may be abstracted into a parameterized fragment after its
  contract and exact expansion theorem are proved;
- literal numeric offsets are allowed when accompanied by a field/range proof;
- named layout offsets may be forced to exact constants with static assertions
  when an external ABI or device format requires them;
- no helper may conceal calls, control-flow exits, faults, memory accesses,
  cancellation points, obligations, or provider requirements.

Source review can display generated syntax, expanded raw instructions, or a
diff between them. Exact artifact identity always follows the expanded form.

## 8. Proof and build economy

Layout theorems are parameterized and reused. Changing one field re-evaluates
the layout value and rechecks only fragments whose typed accesses, stack size,
unwind information, or exported ABI layout depend on it. Callers consuming an
unchanged exported layout hash/contract do not reopen field proofs. Generated
fragments are cached by exact generator code, inputs, target profile, theorem
environment, and checker version; sibling fragments are not invalidated by the
mere existence of a new expansion elsewhere.

Golden fixtures cover empty and nested structs, alignment padding, arrays,
tagged unions, packed rejection, overflow, stack shadow space, odd save sets,
large frames, unwind limits, spill/reload, register renaming, literal-offset
escape, and expansion mutation. Acceptance measures the authored source,
residual goals, generated instruction count, kernel-check work, and invalidation
cone.
