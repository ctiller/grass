# Spike 2: in-memory stable byte-line sort from stdin to Win32 PE

Status: design artifact for review; intentionally not compilable yet.

Authoring view: agents maintain exactly `Spec.lean`, `Assembly.lean`, and
`Program.lean`. The exact snapshot is at the end of this document. Historical
names such as `Bindings.lean` denote generated review projections, not authored
files.

| Proof-economics quantity | Current evidence |
| --- | --- |
| Authored specification | 1 module; 73 physical / 57 nonblank lines |
| Authored realization | 2 modules; 581 physical / 541 nonblank lines |
| Generated expansion/certificates | not generated |
| Clean/incremental checking | not measured |

`Spec.lean` owns the precious contract, `Assembly.lean` owns the selected model,
layout, constructors, data, and literal CFG, and `Program.lean` owns only the
verified closing command and emission request.

This spike asks what a proof of a small `sort` replacement should look like
before its supporting libraries exist. Normative force remains with the owning
documents listed in [README.md](README.md). The portable specification is the
only precious semantic artifact. The selected plan and authored assembly are
reviewed, tuned, replaceable construction inputs; certificates and PE bytes are
derived and rebuilt. In particular, the process population, state partition,
channels, phase topology, and algorithmic weave are not silently promoted into
the specification. They are displayed as a `ProcessPlan`, reviewed as the
program we intend to build, and proved to realize the minimal specification.

The program is the `InMemoryStableSort` milestone: it reads LF-delimited byte strings from standard input, stably orders
them lexicographically by unsigned byte value, and writes each string followed
by LF. It buffers the complete input and all sort metadata before stdout becomes
accessible. If any allocation or checked size computation fails, stdout is
empty and the program terminates with failure. It is a shippable utility for its
declared byte-stream and synchronous-standard-handle profile, not yet a claim of
feature parity with locale-aware or external-storage `sort` implementations.

## 1. The proof we want to read

<!-- grass-block: proof-sketch id=spike2-block-01 -->
```lean
namespace Grass.Spike2

/-!
The format and order are precious choices, not platform accidents:

* LF terminates a record and is not part of its value;
* bytes other than LF—including CR and NUL—are ordinary string bytes;
* a nonempty EOF suffix is one final record;
* empty input has no records;
* output terminates every record with LF, normalizing an unterminated last input;
* comparison is lexicographic over unsigned bytes, with no locale or text decode.
-/
def format : ByteLineFormat := .lfDelimited (.normalizeFinal true)
def order : ByteStringOrder := .lexicographicUnsigned

/-!
All failures are observable as failure but share status one. The audit trace and
proof obligations still distinguish input, allocation, stdout, partial-write,
and zero-progress failures. This exercises concise exhaustive handling without
forcing a bespoke public status for every provider condition.
-/
inductive SortOutcome
  | success | allocationFailure | inputFailure | outputFailure

structure Occurrence where
  ordinal : Nat
  value : ByteArray

def Occurrence.le (left right : Occurrence) : Prop :=
  order.le left.value right.value

def stableSorted (input output : Vec Occurrence) : Prop :=
  output.Permutation input ∧
  output.Pairwise Occurrence.le ∧
  ∀ i j, i < j -> input[i].value = input[j].value ->
    (output.findIdx? input[i]).get! < (output.findIdx? input[j]).get!

/-!
`stable` is an algorithmic demand over input-occurrence identity, not a claim
inferred from output bytes. `silentOnResourceExhaustion` means the stdout trace
is exactly empty for allocation failure or checked address/size exhaustion.
`noArtificialLimit` rejects a fixed application cap: every rejected growth must
be justified by checked representability or a permitted allocator failure.

Termination needs EOF and responsive frontiers. Without eventual EOF, the read
loop is a productive reactive program that reaches another input frontier after
finite internal work; safety does not depend on EOF or responsiveness.
-/
def resources : ConsoleBufferResourceModel :=
  ConsoleBufferResourceModel.untilMemoryExhaustion
    (onExhaustion := .terminateWithNoOutput)
    (capacity := .noArtificialLimit)

def lineStreamFormat : Format (Vec ByteArray) :=
  Console.byteLineStreamFormat format

def lineParserRequirement {R : Type} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement lineStreamFormat

def sortSuite {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : SpecificationSuite resources :=
  Console.stableLineSortSuite
    (resources := resources)
    (format := format) (order := order) (outcomes := SortOutcome)
    (parser := lineParserRequirement resources)

def sortSpec {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (sortSuite resources)
    |>.onResourceExhaustion .allocationFailure
    |>.withLiveness
        (.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem sortSpecCorrect {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : MeetsAllSpecificationTheorems (sortSpec resources) :=
  Console.stableLineSortSuiteCaptureCorrect resources format order SortOutcome
    (lineParserRequirement resources)

theorem successfulTraceIffStableSorted
    {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (sortSpec resources) input output ↔
      StableFormattedOccurrenceOutput format input output stableSorted :=
  Console.stableLineSortContract_success_iff
    resources format order SortOutcome

def spec : SpecProcess resources := sortSpec resources

def policy : TargetOutcomeProjection SortOutcome UInt32 :=
  .successOrFailure
    (success := SortOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

/-!
The standard sequential realizer for `Console.stableSortLines` states the
extensional collect/sort/emit relation. The adapter synthesizes and proves the
expanded process population shown in section 2; both are inspectable output,
not a second application-maintained program.
-/

/-!
This audited value selects synchronous Win32 stdin/stdout, the process heap, and
terminal status. Its inspectable expansion names `GetStdHandle`, `ReadFile`,
`WriteFile`, `GetProcessHeap`, `HeapAlloc`, `HeapReAlloc`, and `ExitProcess`.
No ambient instance search may substitute another allocator or console provider.
-/
def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StandardByteSort projection

/-!
The single authored machine source is in section 6. It contains every input,
allocation, scan, stable-merge, buffered-output, and terminal instruction.
Platform/process realization, block certificates, erasure, encoding, PE layout,
and loading remain inspectable generated witnesses rather than additional
application-maintained pipeline values.
-/
def sortVerified : VerifiedProgram spec := by
  verify_assembly plan
    using_model stableSortModelCorrect
    with sortSource

def bytes : ByteArray := emitProgram sortVerified

-- The fundamental theorem is immediately available as `sortVerified.sound`.

end Grass.Spike2
```

This is the whole intended application surface: two portable format/order
choices, a resource-parameterized specification, one faithful target projection,
one standard sequential adapter theorem, one explicit platform plan, one
assembly source, one closing command, and total emission. `format`, `order`, and
the specification function constitute precious semantic source; `resources` is
the reviewed selected profile.
The synthesized process plan,
platform plan, and `sortSource` may be deleted and rebuilt against it.

## 2. Portable input, output, and stable-order law

The abstract parser is total over every finite byte input:

<!-- grass-block: interface id=spike2-block-02 -->
```lean
def ByteLineFormat.decode : ByteArray -> Vec Occurrence
def ByteLineFormat.encode : Vec Occurrence -> ByteArray

theorem decode_ordinals (input) :
  (format.decode input).map Occurrence.ordinal =
    Vec.range (format.decode input).length
```

For this format:

<!-- grass-block: interface id=spike2-block-03 -->
```text
[]           -> []
"a"          -> ["a"]
"a\n"        -> ["a"]
"\n"         -> [""]
"a\n\n"      -> ["a", ""]
"a\r\nb\n"  -> ["a\r", "b"]
```

Encoding erases ordinals and appends LF to each value. Literal examples are
closed computations for review, not substitutes for universal parser laws.

`StableSorted order input output` is the conjunction of:

- `output` is a permutation of the exact input occurrences;
- adjacent output values are ordered by `order.le`;
- if two input occurrences compare equal and the first has the smaller ordinal,
  the first occurs earlier in `output`.

Occurrence identity matters even when equal strings serialize to identical
bytes. The input parser assigns identities by ordinal, the descriptor
representation connects each ordinal to a physical descriptor, and the merge
proof preserves that connection. Grass may not “prove” stability by observing
that swapping equal serialized strings produces the same stdout bytes.

The portable outcome relation is:

<!-- grass-block: interface id=spike2-block-04 -->
```lean
inductive SortOutcome
  | success
  | allocationFailure
  | inputFailure
  | outputFailure

inductive SortFailureCause
  | stdinUnavailable
  | readFailed
  | resourceExhausted
  | stdoutUnavailable
  | writeFailed
  | noProgress

structure SortObservation (input : ByteArray) where
  stdout : ByteArray
  outcome : SortOutcome
  failureCause : Option SortFailureCause
  status : UInt32

def SortObservation.Accepts (input : ByteArray)
    (o : SortObservation input) : Prop :=
  o.status = policy.status o.outcome ∧
  (match o.outcome with
   | .success =>
       ∃ sorted,
         StableSorted order (format.decode input) sorted ∧
         o.stdout = format.encode sorted
   | .allocationFailure | .inputFailure =>
       o.stdout = #[]
   | .outputFailure =>
       o.stdout.IsPrefixOf
         (format.encode (stableSort order (format.decode input)))) ∧
  AuditCauseMatchesOutcome o.failureCause o.outcome
```

The success clause uses an existential stable-sorted occurrence sequence rather
than trusting a library `stableSort` implementation. The final two clauses use
the uniquely specified sorted byte stream; zero progress is a proper-prefix law
when bytes remain, supplied by the standard write-all contract.

Input is environmental entropy. The theorem quantifies over every finite input,
all read fragmentation, every allowed read failure and EOF point, allocator
success/failure/address choice, every comparison path, every stdout response,
and every admissible load context/base/import environment. Executing examples is
never the proof.

### 2.1 Synthesized sequential process realization

The specification deliberately does not prescribe a pipeline. The application
author does not maintain a second input/allocation/sort/output actor graph.
Instead the canonical adapter elaborates the relational program:

<!-- grass-block: interface id=spike2-block-05 -->
```lean
def sortProcessRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)

theorem sortProcessPlan_realizes :
    ProcessPlanRealizes spec sortProcessRealization.plan :=
  sortProcessRealization.correct
```

The inspectable normalized plan has one root carrying the logical phases
`collecting -> allocatingMetadata -> sorting -> emitting -> terminating`, no
shared regions, standard asynchronous byte-ingress and byte-egress children,
and fresh occurrence-indexed children for provider operations, allocation, and
terminal demands. Positive partial reads append exact chunks to the ingress
stream; line framing is a chunking-invariant consumer above it. Positive partial
writes transfer exact committed prefixes while the egress child retains the
unique suffix. Its generated Hoare channels escrow exact buffer
loans and obligations; every permitted dependent child result and lifecycle
outcome is represented. The pure stable-sort transition stays inside the root
and invokes the reusable extensional `StableSortContract`; it is not made into a
fictional concurrent worker.

The adapter's proof instantiates standard theorems for input-fragment
concatenation, checked allocation, the pre-output allocation barrier, stable
permutation, committed-prefix output, terminal projection, non-vacuous initial
networks, child-choice completeness, global progress, and coupled execution
refinement. Diagnostics expand every generated process kind, channel escrow,
and proof application. An author may replace this with an explicit fused,
parallel, streaming, or external-storage plan while preserving `spec` and the
same `DriverBoundary`.

## 3. Transactional output and progress

The logical process plan proves the allocation/output barrier without mentioning
handles or addresses. The lower process driver refines its five logical phases
to this phase-indexed machine capability:

<!-- grass-block: interface id=spike2-block-06 -->
```lean
inductive SortPhase
  | collecting
  | indexing
  | sorting
  | readyToEmit
  | emitting
  | terminal

class StdoutAuthority : SortPhase -> Type
```

No state before `.readyToEmit` contains `StdoutAuthority`, and the platform rule
for `WriteFile(stdout, ...)` requires it. The stdout handle is not even requested
until all input, descriptor, and scratch allocation has succeeded and sorting is
complete. The resource-exhaustion blocks are reachable only in earlier phases,
so `stdout = #[]` follows from effect exclusion and CFG reachability. There is no
rollback proof. The output buffer is real writable image memory: its active
prefix, writable spare region, pending read loan, and committed stdout
prefix are all represented in the machine state.

Read failure and unavailable stdin also occur before stdout authority and are
therefore silent. Once emission begins there are no allocation operations.
Write failure may expose a prefix because physical stdout is not transactional.
The driver theorem maps each `ReadFile` occurrence to one `readProtocol` child,
each heap request to one `allocationProtocol` child, each partial-write loop to
`outputProtocol` supervising fresh `flushProtocol` children, and `ExitProcess`
to `terminalProtocol`. The complete sort routine is a terminating serial
function/sub-CFG call inside the root transition. Its local Hoare contract is
`StableSortContract`; it creates no demand, occurrence, channel, or scheduler
frontier. The CFG
still proves each concrete occurrence; the process proof does not treat an API
call as atomic or erase pending, partial, failure, or violation branches.

Progress is separated into:

- input collection: finite internal work between `ReadFile` frontiers; EOF is an
  explicit input-provided exit;
- growth: each successful capacity change strictly increases capacity and the
  next read requests a nonempty writable spare slice;
- line scan: input offset strictly increases;
- merge passes: run width strictly increases to the record count, and each inner
  cursor strictly advances;
- output staging: a source cursor advances on every copy, a full 64 KiB buffer
  forces a flush, and a successful partial write advances the flush cursor;
- API pending states: safe without responsiveness, terminating only under the
  named branching-strategy premise.

An infinite input execution is admitted as reactive/productive when it keeps
crossing read frontiers. Conditional whole-program termination additionally
assumes eventual EOF. Internal spin, a zero-size growth request, and successful
zero-byte output while bytes remain each have explicit rejection/failure paths.

## 4. Memory representation and allocation barrier

The implementation uses three process-heap ownership roots:

<!-- grass-block: interface id=spike2-block-07 -->
```lean
structure PhysicalLineDesc where
  offset : UInt64
  length : UInt64

def LineDesc : StructLayout where
  fields := [(`offset, .u64), (`length, .u64)]
  alignment := 8

theorem lineDesc_size : LineDesc.size = 16 := by decide
theorem lineDesc_addr (base index : UInt64) :
  elementAddress LineDesc base index = base + (index <<< 4) := by
  bv_decide

structure SortStorage where
  input : OwnedVec Byte processHeap
  lines : OwnedVec PhysicalLineDesc processHeap
  scratch : OwnedVec PhysicalLineDesc processHeap
  linesRepresent : RepresentsLines format input.value lines.value
  scratchCapacity : scratch.capacity >= lines.length
```

The logical occurrence ordinal is not stored as a third word. Each record's
start offset is unique in the decoded input, and `RepresentsLines` derives the
ordinal from scan order while tying it to that physical offset. Moving a
descriptor moves this ghost occurrence identity with its two physical words.
This keeps the shippable layout at 16 bytes, makes indexed addressing a literal
`index << 4`, and still prevents an unstable swap of equal records from being
proved by relabeling indistinguishable output bytes.

`StructLayout` is a standard `Std.Owned` facility, not a Spike 2 invention. It
generates field offsets, `sizeof`/alignment facts, checked allocation-size
lemmas, and address calculations while leaving the physical field selection and
literal load/store instructions to the assembly author. This spike deliberately
chooses two 64-bit fields: a 16-byte descriptor can represent the full modeled
x64 input extent without the 32-bit cap of a smaller packed alternative. The
source ordinal remains a proof identity derived from the unique record start.

`input` grows while reading. No line descriptor exists until EOF, so
`HeapReAlloc` may replace the byte buffer without invalidating a slice. Its
dependent result is:

<!-- grass-block: interface id=spike2-block-08 -->
```lean
inductive ReallocResult (old : OwnedVec Byte processHeap)
  | success (new : OwnedVec Byte processHeap)
      (fresh : FreshAllocation new.bufferId)
      (prefix : new.value.take old.length = old.value)
      (oldInvalid : ProvenanceInvalid old.bufferId)
  | failed (oldStillOwned : OwnedVec Byte processHeap)
```

The profile separately handles an in-place physical address result: allocation
identity still advances according to the allocator/provenance contract, and no
old pointer may be reused without the returned proof. Failure retains the old
allocation and transfers no ownership.

After EOF, one finite scan counts records using checked arithmetic. Exact-size
`lines` and `scratch` buffers are then allocated before either is read. A second
scan initializes every descriptor with an in-bounds input range and its source
occurrence witness. No descriptor owns bytes; each holds a shared read view subordinate to
the live `input` allocation. Sorting moves typed descriptors and preserves those
views. Untyped copies would require an additional provenance-preservation proof.

Every allocation and multiplication/addition used for capacity or byte size is
checked. `.noArtificialLimit` means the program has no fixed record, line, or
input limit below representability: it requests growth whenever spare capacity
is exhausted. It does not promise that a nondeterministic allocator succeeds
whenever some hypothetical placement exists. Allocation refusal, address-space
exhaustion, and checked representability failure all map to
`.resourceExhausted` before stdout.

Process-heap allocation provenance is distinct from `VirtualAlloc`, stack, or
static-object provenance. At terminal process exit, the Win32 ledger may adopt
these process-owned heap obligations exactly once; borrowed standard handles and
external obligations are not silently adopted.

Output adds one non-heap root:

<!-- grass-block: interface id=spike2-block-09 -->
```lean
def outputBuffer : StaticObject (Array Byte 65536) :=
  static_bss_object (name := `output_buffer) (alignment := 64)

structure BufferedStdoutState where
  used : Fin 65537
  initialized : InitializedRange outputBuffer 0 used
  spare : WritableRange outputBuffer used (65536 - used)
  committed : Vec Byte
  staged : Vec Byte
  represents : outputBuffer.bytes.take used = staged
```

The image loader grants this object one writable static provenance chain; it is
disjoint from input, descriptors, scratch, stack, IAT, and read-only LF data.
Copying extends `initialized` and shrinks `spare`. A `WriteFile` call temporarily
loans the exact suffix `[flushPtr, flushPtr + flushRemaining)` for shared read,
so no append may overlap a pending call. Each positive return consumes the
corresponding loan prefix and appends exactly those bytes to `committed`.
Failure preserves the already committed prefix and makes the uncommitted staged
suffix unobservable; zero progress while bytes remain is an explicit failure.
Only a completed flush re-establishes `used = 0`. The terminal success edge
requires both all sorted records consumed and an empty buffer.

## 5. Stable mergesort contract

The low-level contract is extensional over descriptor identities:

<!-- grass-block: interface id=spike2-block-10 -->
```lean
structure StableSortContract where
  entry : OwnsInitializedVec PhysicalLineDesc lines
        ∗ OwnsInitializedVec PhysicalLineDesc scratch
        ∗ RepresentsLines format inputBytes lines.value
  normal : ∃ final,
      OwnsPermutationOf lines scratch final
    ∧ StableSorted order original final.value
    ∧ RepresentsLines format inputBytes final.value
  faults : OnlyDeclaredFaults
  progress : TerminatesBy MergePassMeasure
```

Spike 2 chooses iterative bottom-up merge sort because its proof boundary is
small and its allocation is complete before sorting. The reusable merge theorem
owns cursor bounds, permutation, initialization transfer, and run concatenation.
The assembly author owns the actual compare loop and the tie rule:

<!-- grass-block: interface id=spike2-block-11 -->
```text
compare(left.value, right.value)
  less    -> take left
  equal   -> take left   ; the stable choice
  greater -> take right
```

After each pass, source and destination descriptor arrays swap roles. A pass
invariant states that both arrays remain owned, exactly one prefix of the
destination is initialized for the current pass, completed runs are stable and
sorted, and untouched source descriptors retain their read views. The pass
measure is lexicographic in remaining runs and remaining elements. Run width
doubles with checked saturation at `lineCount`; overflow cannot create a loop.

`verify_asm` symbolically proves ordinary compare/copy blocks against this
contract. The standard merge combinator supplies routine slice and permutation
algebra. The author must still state the merge/pass invariants, select the left
element on equality, and provide measures. A novel SIMD, radix, network, or
in-place implementation may replace the entire sub-CFG by proving the same
`StableSortContract`; it need not resemble mergesort.

Descriptor construction and the merge copy contain no manual occurrence
annotations. `LineDesc` plus the scan/merge invariants identifies each
whole initialized element, and the verifier transports its ordinal occurrence
through the literal scalar loads/stores. Replacing those two loads/stores by one
proved 128-bit move changes the local instruction proof but not the logical
permutation argument. A partial, overlapping, or type-punning copy would instead
leave an explicit refinement goal.

Two assembly implementations satisfying this contract are automatically
equivalent under the specification's observation filter and mandatory stable
identity theorem. Optimization does not re-prove input parsing, provider laws,
or PE loading.

The exact proof boundary is not merely the top-level console relation:

<!-- grass-block: interface id=spike2-block-12 -->
```lean
def stableSortModel : ImplementationModel :=
  StableSort.bottomUpModel format order

theorem stableSortModel_correct :
  ImplementationRealizesContract stableSortModel
    (StableSortContract format order)

theorem sortSource_refines_model :
  AssemblyRefinesImplementation
    sortAlgorithmScope lineDescRepresentation stableSortModel

theorem stableSort_contract_connects :
  ComponentContractRefinesRequirement
    (StableSortContract format order) sortRequirement
```

`stableSortModel_correct` owns stable permutation/order mathematics once.
The assembly theorem owns descriptor representation and literal merge control
inside `sortAlgorithmScope`. Parsing, I/O fragmentation, allocation failure,
terminal policy, and progress remain separate program/driver requirements and
are composed through `stableSort_contract_connects`; the pure model does not
pretend to prove them. A SIMD or radix implementation may refine the same
extensional model or supply a new proved model without reopening provider,
process, or PE proofs.

The expected source marks the sort region with its selected model contract;
`verify_assembly` derives and reports the corresponding
`ImplementationBinding` from the exact source scope, descriptor representation,
banked model certificate, assembly-to-model theorem, and component-to-program
theorem. A merge-body edit first invalidates
`sortSourceRefinesModel`; a model-contract edit first invalidates
`stableSortContractConnects` and its consumers. The fixture records and checks
those first-invalidated boundaries in `sortBindingMutationExpectations`.

## 6. The authored Win32 x64 CFG

This is the complete intended machine source. It is one authored `asm_source`;
generated `ImplementsBlock` and `SubCFG.plug` values are diagnostics. The
local reusable forms used below are typed Lean fragment constructors, not a
textual preprocessor and not semantic shortcuts: their complete expansions
follow the main CFG.

The comment-free fixture keeps layouts, constructors, static data, and the CFG
in `Assembly.lean`. The elaborator combines the exact constructor closure,
static-object table, derived import table, and authored source as a generated
`sortSourceClosure`, derives `sortExpandedSource`, and proves
`sortExpansionExact : SourceElaboratesExactlyTo sortSourceClosure
sortExpandedSource`. `sortSourceClosureComplete` rejects unresolved constructor,
symbol, import, and helper references; `sortExpandedListingExact` ties the
review listing to the generated raw instruction value. Only that expanded
source reaches verification and emission.

The author declares the frame by name rather than maintaining displacement
arithmetic by hand:

<!-- grass-block: proof-sketch id=spike2-block-13 -->
```lean
def SortFrame : FrameLayout Win64 := frame_layout {
  shadow          : bytes 32
  arg5             : UInt64
  ioCount          : UInt32
  ioRequest        : UInt32
  stdin            : UInt64
  stdout           : UInt64
  lines            : UInt64
  scratch          : UInt64
  lineCount        : UInt64
  width            : UInt64
  left             : UInt64
  mid              : UInt64
  right            : UInt64
  i                : UInt64
  j                : UInt64
  k                : UInt64
  appendPtr        : UInt64
  appendRemaining  : UInt64
  outputIndex      : UInt64
  finalDescriptors : UInt64
  outUsed          : UInt64
  savedRsi         : UInt64
  savedRdi         : UInt64
  flushPtr         : UInt64
  flushRemaining   : UInt64
  size := 216
}
```

`FrameLayout.derive SortFrame` gives, in declaration order, exact offsets
`0,32,40,44,48,56,64,72,80,88,96,104,112,120,128,136,144,152,160,168,176,184,192,200,208`.
It proves field non-overlap, stack ownership, the 216-byte extent, call-site
alignment after eight pushes, and the unwind description. The assembly source
uses operands such as `[rsp+SortFrame.stdout]`; lowering produces literal
`[rsp+56]`. The table, representative derived comments, and fully lowered constructor
expansions keep the exact instructions reviewable. An author may instead write
`[rsp+56]` as a literal override, in which case the verifier checks that address
directly without pretending it follows the named layout. Adding or reordering a field
therefore changes the layout declaration and derived operands, not dozens of
hand-maintained constants.

The output buffer is a distinct 65,536-byte, 64-byte-aligned writable static
object. It is not an allocator result and introduces no allocation-failure path.
Its PE mapping creates writable static provenance for exactly that object.

<!-- grass-block: proof-sketch id=spike2-block-14 -->
```text
def sortSource : AsmSource plan := asm_source {

entry:
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, SortFrame.size               ; derived immediate 216
    call qword ptr [rip + __imp_GetProcessHeap]
    test rax, rax
    jz   resource_exhausted
    mov  r12, rax                         ; process heap
    mov  ecx, STD_INPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdin_unavailable
    cmp  rax, INVALID_HANDLE_VALUE
    je   stdin_unavailable
    mov  qword ptr [rsp+SortFrame.stdin], rax ; derived +48; borrowed handle
    xor  r13d, r13d                       ; input pointer
    xor  r14d, r14d                       ; input length
    xor  r15d, r15d                       ; input capacity
    jmp  read_head

read_head: @placement [input := r13, length := r14, capacity := r15]
           @invariant growable_input_vec
           @frontier_or_measure(read_or_growth)
    cmp  r14, r15
    je   grow_input
read_issue:
    ; establish a unique write loan over input[len..cap]
    mov  rax, r15
    sub  rax, r14                         ; spare, proved positive
    mov  r8d, 0xffffffff                  ; ReadFile's DWORD request ceiling
    cmp  rax, r8
    cmovb r8, rax
    test r8d, r8d
    jz   grow_input                       ; defensive; unreachable from invariant
    mov  dword ptr [rsp+SortFrame.ioRequest], r8d ; derived +44
    mov  rcx, qword ptr [rsp+SortFrame.stdin]     ; derived +48
    lea  rdx, [r13+r14]
    lea  r9, [rsp+SortFrame.ioCount]       ; derived +40; bytesRead
    mov  dword ptr [rsp+SortFrame.ioCount], 0
    mov  qword ptr [rsp+SortFrame.arg5], 0 ; derived +32; null OVERLAPPED
    call qword ptr [rip + __imp_ReadFile]
    test eax, eax
    jz   read_failed
    mov  eax, dword ptr [rsp+SortFrame.ioCount]
    cmp  eax, dword ptr [rsp+SortFrame.ioRequest]
    ja   provider_violation @violation_edge(.excessReadCount)
    test eax, eax
    jz   input_eof
    add  r14, rax
    jmp  read_head

grow_input: @placement [input := r13, length := r14, capacity := r15]
            @invariant growable_input_vec
            @measure representable_capacity_remaining
    test r15, r15
    jnz  grow_existing
    mov  ebx, 4096                        ; reviewed growth-policy choice
    mov  rcx, r12
    xor  edx, edx                         ; HeapAlloc flags
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  r13, rax
    mov  r15, rbx
    jmp  read_issue

grow_existing:
    mov  rbx, -1
    shr  rbx, 1                           ; UInt64.max / 2
    cmp  r15, rbx
    ja   grow_saturate
    mov  rbx, r15
    shl  rbx, 1                           ; checked geometric growth
    jmp  grow_realloc
grow_saturate:
    mov  rbx, -1
    cmp  r15, rbx
    je   resource_exhausted               ; representability is exhausted
grow_realloc:
    mov  rcx, r12
    xor  edx, edx                         ; HeapReAlloc flags
    mov  r8, r13                          ; old allocation remains owned on NULL
    mov  r9, rbx
    call qword ptr [rip + __imp_HeapReAlloc]
    test rax, rax
    jz   resource_exhausted               ; r13 still denotes the owned old buffer
    mov  r13, rax                         ; dependent success consumes old identity
    mov  r15, rbx
    jmp  read_issue

input_eof:
    xor  ebp, ebp                         ; line count
    xor  ebx, ebx                         ; byte index
    test r14, r14
    jz   no_descriptors
count_loop: @placement [input := r13, inputLength := r14,
                        cursor := rbx, lineCount := rbp]
            @invariant count_lf_prefix
            @measure r14-rbx
    cmp  rbx, r14
    jae  count_suffix
    cmp  byte ptr [r13+rbx], 10
    jne  count_next
    add  rbp, 1
    jc   resource_exhausted
count_next:
    add  rbx, 1
    jc   resource_exhausted
    jmp  count_loop
count_suffix:
    lea  rax, [r14-1]
    cmp  byte ptr [r13+rax], 10
    je   allocate_descriptors
    add  rbp, 1
    jc   resource_exhausted

allocate_descriptors:
    mov  rbx, rbp
    shl  rbx, 4                           ; exact 16-byte descriptor size
    mov  rax, rbx
    shr  rax, 4
    cmp  rax, rbp
    jne  resource_exhausted
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  rdi, rax
    mov  qword ptr [rsp+SortFrame.lines], rax ; derived +64
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted               ; lines remain process-owned
    mov  rsi, rax
    mov  qword ptr [rsp+SortFrame.scratch], rax ; derived +72
    jmp  descriptor_scan_init

no_descriptors:
    xor  edi, edi
    xor  esi, esi
    mov  qword ptr [rsp+SortFrame.lines], 0
    mov  qword ptr [rsp+SortFrame.scratch], 0
    mov  qword ptr [rsp+SortFrame.lineCount], 0
    mov  qword ptr [rsp+SortFrame.finalDescriptors], 0
    jmp  sort_done

descriptor_scan_init:
    mov  qword ptr [rsp+SortFrame.lineCount], rbp ; derived +80
    xor  r8d, r8d                         ; current byte
    xor  r9d, r9d                         ; record start
    xor  r10d, r10d                       ; descriptor/source ordinal
descriptor_scan: @placement [cursor := r8, lineStart := r9, index := r10]
                 @invariant represents_scanned_prefix
                 @measure r14-r8
    cmp  r8, r14
    jae  descriptor_suffix
    cmp  byte ptr [r13+r8], 10
    jne  descriptor_next_byte
    mov  rax, r10
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  qword ptr [rdx + LineDesc.offset], r9
    mov  rcx, r8
    sub  rcx, r9
    mov  qword ptr [rdx + LineDesc.length], rcx
    add  r10, 1
    add  r8, 1
    mov  r9, r8
    jmp  descriptor_scan
descriptor_next_byte:
    add  r8, 1
    jmp  descriptor_scan
descriptor_suffix:
    cmp  r9, r14
    jae  descriptor_scan_done
    mov  rax, r10
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  qword ptr [rdx + LineDesc.offset], r9
    mov  rcx, r14
    sub  rcx, r9
    mov  qword ptr [rdx + LineDesc.length], rcx
    add  r10, 1
descriptor_scan_done:
    cmp  r10, rbp
    jne  internal_fault                    ; proved unreachable consistency check
    mov  qword ptr [rsp+SortFrame.width], 1 ; derived +88
    jmp  sort_pass

sort_pass: @contract StableSortContract
           @invariant stable_merge_pass(input, lines, scratch)
           @measure merge_pass_measure
    mov  rax, qword ptr [rsp+SortFrame.width]
    cmp  rax, rbp
    jae  sort_complete
    mov  qword ptr [rsp+SortFrame.left], 0 ; derived +96
merge_run_head:
    mov  rax, qword ptr [rsp+SortFrame.left]
    cmp  rax, rbp
    jae  merge_pass_done
    mov  rcx, rax
    add  rcx, qword ptr [rsp+SortFrame.width]
    cmp  rcx, rbp
    cmova rcx, rbp
    mov  qword ptr [rsp+SortFrame.mid], rcx ; derived +104
    mov  rdx, rcx
    add  rdx, qword ptr [rsp+SortFrame.width]
    cmp  rdx, rbp
    cmova rdx, rbp
    mov  qword ptr [rsp+SortFrame.right], rdx ; derived +112
    mov  qword ptr [rsp+SortFrame.i], rax     ; derived +120
    mov  qword ptr [rsp+SortFrame.j], rcx     ; derived +128
    mov  qword ptr [rsp+SortFrame.k], rax     ; derived +136
merge_choose: @invariant stable_merge_cursors(i,j,k)
              @measure (mid-i)+(right-j)
    mov  rax, qword ptr [rsp+SortFrame.i]
    cmp  rax, qword ptr [rsp+SortFrame.mid]
    jae  merge_drain_right
    mov  rcx, qword ptr [rsp+SortFrame.j]
    cmp  rcx, qword ptr [rsp+SortFrame.right]
    jae  merge_drain_left
    shl  rax, 4
    lea  rdx, [rdi+rax]                   ; left descriptor
    mov  rax, rcx
    shl  rax, 4
    lea  r8, [rdi+rax]                    ; right descriptor
    $(compareRecords rdx r8)
    cmp  eax, 0
    jle  merge_take_left                  ; equality is the stable choice
merge_take_right:
    mov  rax, qword ptr [rsp+SortFrame.j]
    add  qword ptr [rsp+SortFrame.j], 1
    jmp  merge_copy
merge_take_left:
    mov  rax, qword ptr [rsp+SortFrame.i]
    add  qword ptr [rsp+SortFrame.i], 1
merge_copy:
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  rax, qword ptr [rsp+SortFrame.k]
    shl  rax, 4
    lea  r8, [rsi+rax]
    mov  rcx, qword ptr [rdx + LineDesc.offset]
    mov  qword ptr [r8 + LineDesc.offset], rcx
    mov  rcx, qword ptr [rdx + LineDesc.length]
    mov  qword ptr [r8 + LineDesc.length], rcx
    add  qword ptr [rsp+SortFrame.k], 1
    jmp  merge_choose
merge_drain_left:
    mov  rax, qword ptr [rsp+SortFrame.i]
    cmp  rax, qword ptr [rsp+SortFrame.mid]
    jae  merge_run_done
    add  qword ptr [rsp+SortFrame.i], 1
    jmp  merge_copy
merge_drain_right:
    mov  rax, qword ptr [rsp+SortFrame.j]
    cmp  rax, qword ptr [rsp+SortFrame.right]
    jae  merge_run_done
    add  qword ptr [rsp+SortFrame.j], 1
    jmp  merge_copy
merge_run_done:
    mov  rax, qword ptr [rsp+SortFrame.right]
    mov  qword ptr [rsp+SortFrame.left], rax
    jmp  merge_run_head
merge_pass_done:
    xchg rdi, rsi
    mov  rax, qword ptr [rsp+SortFrame.width]
    add  rax, rax
    cmp  rax, rbp
    cmova rax, rbp
    mov  qword ptr [rsp+SortFrame.width], rax
    jmp  sort_pass
sort_complete:
    mov  qword ptr [rsp+SortFrame.finalDescriptors], rdi ; derived +168

sort_done:
    mov  ecx, STD_OUTPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdout_unavailable
    cmp  rax, INVALID_HANDLE_VALUE
    je   stdout_unavailable
    mov  qword ptr [rsp+SortFrame.stdout], rax ; derived +56
                                             ; StdoutAuthority .readyToEmit
    mov  qword ptr [rsp+SortFrame.outputIndex], 0 ; derived +160
    mov  qword ptr [rsp+SortFrame.outUsed], 0     ; derived +176
    jmp  emit_head

emit_head: @invariant sorted_occurrence_consumer(finalDescriptors)
           @invariant buffered_stdout(output_buffer, outUsed, committedPrefix)
           @measure remaining_source_bytes_plus_records
    mov  rax, qword ptr [rsp+SortFrame.outputIndex] ; derived +160
    cmp  rax, rbp
    jae  emit_final_flush
    shl  rax, 4
    add  rax, qword ptr [rsp+SortFrame.finalDescriptors] ; derived +168
    mov  rdx, qword ptr [rax + LineDesc.offset]
    add  rdx, r13
    mov  r8, qword ptr [rax + LineDesc.length]
    $(bufferAppend rdx r8)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    lea  rdx, [rip + lf_byte]
    mov  r8d, 1
    $(bufferAppend rdx r8)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    add  qword ptr [rsp+SortFrame.outputIndex], 1 ; derived +160
    jmp  emit_head

emit_final_flush:
    $(flushOutput)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    jmp  exit_success

stdin_unavailable:   @terminal(.inputFailure) @audit(.stdinUnavailable)
    $(failureExit .inputFailure)
read_failed:         @terminal(.inputFailure) @audit(.readFailed)
    $(failureExit .inputFailure)
resource_exhausted:  @terminal(.allocationFailure) @audit(.resourceExhausted)
    $(failureExit .allocationFailure)
stdout_unavailable:  @terminal(.outputFailure) @audit(.stdoutUnavailable)
    $(failureExit .outputFailure)
write_failed:        @terminal(.outputFailure) @audit(.writeFailed)
    $(failureExit .outputFailure)
no_progress:         @terminal(.outputFailure) @audit(.noProgress)
    $(failureExit .outputFailure)
exit_success:       @terminal(.success)
    xor ecx, ecx
exit:
    call qword ptr [rip + __imp_ExitProcess]
    ud2 @containment_tail(.terminalUnexpectedReturn)
provider_violation:
    ud2 @containment_tail(.returnedCountExceedsRequest)
internal_fault:
    ud2 @containment_tail(.provedUnreachable)

rodata {
lf_byte: db 10
}

bss {
align 64
output_buffer: resb 65536
}
}
```

The following is a historical handwritten proof sketch, not the exact expansion
of the current authored `compareRecords`. The current source performs address
formation in a different instruction order and uses `add` rather than the shown
`lea` sequence. It remains only to expose the demanded shape until one
canonical generated raw manifest replaces it; it must not be cited as expansion
evidence.

<!-- grass-block: proof-sketch id=sort-compare-expansion-obsolete -->
```text
mov  rax, qword ptr [rdx+0]
mov  r10, qword ptr [rdx+8]
mov  rcx, qword ptr [r8+0]
mov  r11, qword ptr [r8+8]
lea  rax, [r13+rax]
lea  rcx, [r13+rcx]
xor  r9d, r9d
.compare_loop:
    cmp  r9, r10
    jae  .left_end
    cmp  r9, r11
    jae  .less
    movzx edx, byte ptr [rax+r9]
    movzx r8d, byte ptr [rcx+r9]
    cmp  edx, r8d
    jb   .less
    ja   .greater
    add  r9, 1
    jmp  .compare_loop
.left_end:
    cmp  r9, r11
    jb   .less
    xor  eax, eax
    jmp  .done
.less:    mov eax, -1; jmp .done
.greater: mov eax,  1
.done:
```

It performs no call and changes only volatile registers. Bounds for both byte
loads come from the two physical descriptors and `RepresentsLines`.

`$(bufferAppend pointer length)` stages an arbitrary-size slice in the
64 KiB static object. A record longer than the buffer crosses the flush backedge
as many times as necessary; there is no line-size cap. The following is likewise
a non-authoritative proof sketch. It still contains `$(flushOutput)` and
uninstantiated local labels, so it is neither fully expanded nor hygienically
instantiated. The final generator must print every instance with numeric
operands and unique labels.

For a conforming provider that completes each request in full, a successful run
with `n` output bytes performs exactly `ceil(n / 65536)` `WriteFile` calls (zero
when `n = 0`), independent of record count. Permitted partial writes add only the
calls necessary to drain those same buffer slices; they never restore the old
two-calls-per-record behavior.

<!-- grass-block: proof-sketch id=sort-buffer-append-expansion-obsolete -->
```text
mov  qword ptr [rsp+184], rsi             ; savedRsi
mov  qword ptr [rsp+192], rdi             ; savedRdi
mov  qword ptr [rsp+144], pointer         ; appendPtr
mov  qword ptr [rsp+152], length          ; appendRemaining
.append_head:
    cmp  qword ptr [rsp+152], 0
    je   .append_complete
    cmp  qword ptr [rsp+176], 65536       ; outUsed
    jb   .append_have_room
    $(flushOutput)                         ; expands to the block shown below
    test eax, eax
    jnz  .append_restore                  ; 1 = failure, 2 = no progress
    jmp  .append_head
.append_have_room:
    mov  rcx, 65536
    sub  rcx, qword ptr [rsp+176]         ; available
    mov  rax, qword ptr [rsp+152]
    cmp  rax, rcx
    cmovb rcx, rax                        ; chunk = min(remaining, available)
    mov  r10, rcx                         ; rep movsb consumes rcx
    mov  rsi, qword ptr [rsp+144]
    lea  rdi, [rip + output_buffer]
    add  rdi, qword ptr [rsp+176]
    cld                                    ; explicit ABI-required copy direction
    rep movsb
    mov  qword ptr [rsp+144], rsi
    sub  qword ptr [rsp+152], r10
    add  qword ptr [rsp+176], r10
    jmp  .append_head
.append_complete:
    xor  eax, eax
.append_restore:
    mov  rsi, qword ptr [rsp+184]
    mov  rdi, qword ptr [rsp+192]
```

`$(flushOutput)` is not one `WriteFile`: it is the complete partial-write
loop below. It is inlined hygienically at each invocation, including the one
inside `bufferAppend` and the final flush before success.

<!-- grass-block: proof-sketch id=sort-flush-expansion-obsolete -->
```text
lea  rax, [rip + output_buffer]
mov  qword ptr [rsp+200], rax             ; flushPtr
mov  rax, qword ptr [rsp+176]
mov  qword ptr [rsp+208], rax             ; flushRemaining
.flush_head:
    cmp  qword ptr [rsp+208], 0
    je   .flush_complete
    mov  eax, dword ptr [rsp+208]         ; <= 65536 by buffer invariant
    mov  dword ptr [rsp+44], eax          ; exact request
    mov  rcx, qword ptr [rsp+56]          ; stdout
    mov  rdx, qword ptr [rsp+200]
    mov  r8d, dword ptr [rsp+44]
    lea  r9, [rsp+40]                     ; bytesWritten
    mov  dword ptr [rsp+40], 0
    mov  qword ptr [rsp+32], 0            ; null OVERLAPPED
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   .flush_failed
    mov  eax, dword ptr [rsp+40]
    cmp  eax, dword ptr [rsp+44]
    ja   provider_violation @violation_edge(.excessWriteCount)
    test eax, eax
    jz   .flush_stalled
    add  qword ptr [rsp+200], rax
    sub  qword ptr [rsp+208], rax
    jmp  .flush_head
.flush_complete:
    mov  qword ptr [rsp+176], 0
    xor  eax, eax
    jmp  .flush_done
.flush_failed:
    mov  eax, 1
    jmp  .flush_done
.flush_stalled:
    mov  eax, 2
.flush_done:
```

Fragment expansion is required to occur before CFG verification and erasure;
it has not yet been generated for this design corpus. When implemented, the expanded
instructions, hygienic labels, violation edge, encodings, and proof obligations
are inspectable. An author may inline or replace any constructor. No scan, compare,
merge, allocation, API, output, or terminal helper body is omitted.

The constructor result types declare these effects explicitly. `compareRecords` clobbers
`rax, rcx, rdx, r8, r9, r10, r11` and flags, has one internal backedge, and
touches only its two represented read slices. `bufferAppend` clobbers the
Win64 volatile set, flags, and temporary `rsi/rdi` values which it saves and
restores; it requires the exact source slice readable and the destination spare
range writable; it owns frame fields `appendPtr`, `appendRemaining`, `savedRsi`,
`savedRdi`, and the fields delegated to `flushOutput`; it has the append and
full-buffer backedges and may take every flush exit. `flushOutput` clobbers the
Win64 volatile set and flags, owns `arg5`, `ioCount`, `ioRequest`, `flushPtr`,
and `flushRemaining`, has the displayed partial-write backedge, and may pend,
fail, report no progress, or enter the narrow excess-count violation edge. Both
constructors have zero additional stack footprint beyond `SortFrame`; neither changes
`rsp`; both preserve all nonvolatile registers at their public exits. Hygiene
alone proves none of this—the expanded CFG is checked against the declarations.

Each declaration is universally quantified over its legal operands and frame
placement. Its theorem is checked once for the generated sequence family; an
application such as `$(compareRecords rdx r8)` contributes only operand typing,
entry-contract matching, and exit-contract composition. The closed source still
retains the exact expansion used for CFG discovery and encoding.

`$(failureExit outcome)` is a proved fragment constructor expanding to
`mov ecx, policy.status(outcome); jmp exit` for the incoming terminal tag. Its
raw instructions and encoding remain inspectable, and an author may inline or
replace it. The constructor removes repeated status bookkeeping without inferring
which semantic outcome occurred.

The generated graph retains call pending, narrow violation-envelope, ordinary
failure, architectural fault/interruption, terminal, and impossible-return
exits. Each direct edge locally satisfies the target entry contract. Standard
Win64 automation derives shadow space, stack-slot loans, saved-register framing,
and unwind metadata from the literal prologue plus `SortFrame`. Changing the
frame declaration, registers, or prologue regenerates the affected operands,
local certificates, and `.xdata`, not the sort specification or unrelated block
proofs. A literal displacement override is intentionally part of the incident
assembly block's invalidation cone.

## 7. Provider and ABI proof burden

The synchronous stdin provider has the same explicit context issue as stdout:
a standard handle used with null `OVERLAPPED*` must satisfy the selected profile's
synchronous-access requirement. Both requirements bubble into
`AdmissibleExecutionContext sortVerified.realization`; they are neither assumed
from non-null handles nor hidden by the standard plan.

This restriction is part of the declared initial product profile. Consequently
the emitted artifact must not be marketed as a universal drop-in Windows
replacement: inherited handles opened for overlapped I/O are outside its
admissible executions. A production-general Win32 plan must probe or implement
the appropriate overlapped protocol and prove that provider refines this same
portable byte-stream specification. That extension changes the plan/provider
and assembly I/O blocks, not the precious sort semantics.

`ReadFile` models every permitted dependent result:

- unavailable/invalid handle before the read loop;
- pending indefinitely;
- failure with its cited output-slot guarantees;
- successful positive count no greater than the requested writable slice;
- successful zero at EOF under the selected byte-stream provider profile;
- a narrow excess-count violation envelope for optional containment;
- interruption/cancellation and device distinctions required by its citations.

The abstract stdin provider proves that arbitrary physical fragmentation
concatenates to the same finite byte input at EOF. It must not infer EOF from a
zero count unless the selected cited handle/profile contract licenses that rule.
Alternative pipe/console providers may expose a different completion protocol
while refining the same portable input effect.

`WriteFile` is proved against the exact current flush slice, not against a
fictional atomic stream append. Its dependent result includes pending, failure,
every positive count at most the request, successful zero/no-progress, and the
narrow excess-count violation envelope. On each positive partial return the
trace commits precisely that prefix and the assembly advances `flushPtr` and
`flushRemaining`; it neither duplicates nor skips bytes. Requests are nonzero
and at most 65,536, so the DWORD conversion is exact. The final-success contract
requires `outUsed = 0`, making omission of the last partial buffer locally
untypable.

The process-heap profile models `GetProcessHeap`, `HeapAlloc`, and `HeapReAlloc`
with flags zero, alignment, maximum sizes, same-address and moved success,
failure preserving old ownership, provenance renewal, initialization state, and
terminal adoption. Fuzzers and probes challenge each dependent branch but never
replace its theorem.

The terminal provider proves status zero/one preservation, program-relative
reflection, distinguishability, pending/terminal behavior, and process-owned
heap obligation adoption. The responsiveness bridge universally couples every
concrete branching-strategy continuation to the exact abstract strategy used by
the EOF/API responsiveness theorem.

## 8. Erasure, PE emission, and the public theorem

`verify_assembly plan using_component sortImplementationBinding
using_source_closure sortSourceClosureComplete using_expansion
sortExpansionExact with sortExpandedSource`
closes two distinct refinements. First, the uniquely selected standard
sequential realizer plus the standard
`SequentialAdapter` prove that the generated population, escrows, and coupled
executions realize the precious `spec`. Second, the generated source certificate
proves that the exact Win32/x86 driver and authored blocks realize that process
plan under `plan`.
Neither proof is inferred from naming similarity. The closure rejects a source
that sorts correctly but attaches a read response to the wrong child identity,
enables output before the allocation barrier, loses a committed flush prefix, or
reaches a terminal status not licensed by the process outcome.

Ghost operations track vector phases, loans, descriptor occurrence identities,
stable runs, merge initialization, buffered-output state, stdout authority, and
obligations. Erasure retains exactly the authored x86 instructions, static LF
byte, writable zero-fill output object, selected calls, symbols, and relocations.
Its owned theorem is:

<!-- grass-block: proof-sketch id=spike2-block-18 -->
```lean
theorem sort_erasure :
  ErasurePreservesSemantics
    sortVerified.ghostProgram sortVerified.rawProgram :=
  sortVerified.erasureCorrectness
```

The PE linker derives:

- `.text` from the erased CFG, `R-X`;
- `.rdata` containing only required static constants such as LF, `R--`;
- a 64-byte-aligned `output_buffer` in the zero-fill virtual tail of writable,
  non-executable `.data`; it contributes 65,536 bytes of loaded image memory but
  not 65,536 initialized bytes to the PE file;
- `.idata` containing exactly the seven selected Win32 imports;
- writable IAT during loading and standard final permissions;
- `.pdata`/`.xdata` from every non-leaf prologue;
- ASLR-safe RVA/RIP-relative references, `DYNAMIC_BASE`, and `NX_COMPAT`;
- no exports, TLS callbacks, or unrelated runtime.

The artifact certificate proves the `.data` RVA, 65,536-byte virtual extent,
alignment, zero-fill mapping, non-overlap, relocation-safe RIP-relative
references, and `RW-` permissions. The loader theorem creates exactly the
writable static provenance used by `BufferedStdoutState`; executable or
read-only mapping of that object fails artifact verification.

Writer/reader, parser-correctness, semantic decode, loader, and exact-byte
connection laws use only canonical certificate projections:

<!-- grass-block: proof-sketch id=spike2-block-19 -->
```lean
theorem emission_exact :
  emitProgram sortVerified = PE.write sortVerified.linkedArtifact

theorem pe_round_trip :
  PE.parse (emitProgram sortVerified) = .ok sortVerified.linkedArtifact

theorem sort_emitted_sound := sortVerified.sound
```

`sortVerified.sound` quantifies over the canonical admissible context, load-base,
and import domains. For every loaded modeled execution it supplies universal
prefix safety, trace refinement, ABI/obligation correctness, and applicable
progress. A finite terminal result additionally satisfies `SortObservation`;
an infinite read/pending trace has no fabricated terminal observation.
Conditional termination applies universally only under eventual EOF and the
responsive branching strategy. General environment violations receive only the
maximal pre-violation safe prefix; narrow containment theorems separately
consume their exact return envelopes.

## 9. Proof locality and expected change cost

| Change | Expected author edits | Rebuilt derived cone |
| --- | --- | --- |
| input examples or runtime data | none | no static program proof; theorem already universal |
| line format or comparison order | precious spec plus reusable parser/sort relation instantiations; assembly only where semantics truly changed | sequential-adapter refinement, affected parse/compare/sort certificates, outer `VerifiedProgram spec`, and downstream artifact |
| replace synthesized plan with an explicit population/weave | explicit plan and its composition proof; source only where the stable boundary changes | affected channel/ownership/progress certificates and process-to-source refinement; precious spec and unrelated boundary-parametric blocks remain |
| standard read/allocation/flush/terminal protocol law | standard-library protocol theorem and affected driver refinement | every plan and source certificate depending on that law; precious specifications remain unless their observations changed |
| status one becomes another value | one literal terminal instruction, or zero edits with a symbolic `$policy.status(.failure)` operand | terminal check, encoding/layout, terminal protocol demanded subset |
| input growth strategy | local growth blocks/invariants and their allocation-driver refinement | input storage/source certificates and downstream assembly/artifact; process plan and sort law remain |
| mergesort optimization/register allocation | changed sort sub-CFG and genuinely new invariants/measures | incident block, pure-sort driver certificate, unwind/encoding/layout, and stable contract composition; process plan remains |
| output buffer size or copy strategy | `output_buffer` declaration, buffer contract, and output sub-CFG only | output/flush driver and block certificates plus `.data` layout/RVA and downstream artifact; process plan, parser, comparator, merge, and heap proofs remain |
| add/reorder a stack local | `SortFrame` declaration and any blocks that name that field | derived displacements, incident block encodings, frame/non-overlap proof and `.xdata`; no manual unrelated offset edits |
| Win32 to Linux/another ISA | platform plan and authored machine source | process-driver/provider/ABI/ISA/artifact chain; precious sort spec and process plan unchanged when the same weave is retained |
| synchronous-only to adaptive/overlapped Win32 I/O | Win32 provider selection and I/O sub-CFGs | context domain, provider/ABI proofs, I/O blocks and artifact; precious sort spec and pure sorting contract unchanged |

Changing one merge block must not reopen line parsing, process composition,
provider realization, or untouched output proofs. Changing only the process
weave must not edit the precious sort relation, but it must re-prove composition
and every changed process/source boundary. Changing the precious ordering must
reopen the standard sequential realization, its adapter instantiation, the compare and stable-sort contracts, and the
outer `VerifiedProgram spec` even if old machine bytes happen to produce the
same result on tests. The build reports the invalidation cone before rebuilding.

## 10. Adversarial review questions

Before implementation, reviewers should try to:

- make allocation fail after a stdout event;
- make an internal process event escape the observation filter or disappear
  without its required ownership transfer;
- attach a read, allocation, flush, or terminal response to the wrong child ID;
- smuggle process count, mergesort pass shape, buffer size, Win32 vocabulary, or
  exact routing into the precious specification;
- let two logical processes mutate a value while `SharedRegion := Empty`;
- change the process weave while reusing an old composition or source-refinement
  certificate;
- hide a fixed input/record/line cap behind capacity arithmetic;
- lose the old buffer on failed `HeapReAlloc` or revive its provenance on move;
- create line descriptors before the final input allocation moves;
- read uninitialized spare capacity or descriptor slots;
- overflow capacity, descriptor count, `count * sizeof(PhysicalLineDesc)`, or run width;
- reorder equal occurrence identities while emitting indistinguishable bytes;
- let an unstable comparator satisfy only the stdout projection;
- fabricate EOF from a provider behavior that does not promise it;
- make one favorable responsive run prove termination for all runs;
- emit a partial result on allocation or input failure;
- treat output failure as atomic or discard its committed prefix;
- return success with staged bytes still in the output buffer;
- duplicate or skip bytes across a partial flush, or overwrite a pending read loan;
- impose a 64 KiB line limit instead of cycling append/copy/flush;
- let a frame edit silently retain one stale literal displacement;
- adopt an external obligation at process exit;
- type a containment tail after an arbitrary memory/ABI/control violation;
- prove a nearby PE/raw program while emitting different bytes; or
- make a spec/order change trigger monolithic unrelated proof churn.

Reviewers must also decide whether this is a program worth shipping for its
stated `InMemoryStableSort` scope. In particular, challenge whole-input buffering,
the two 16-byte descriptor arrays (32 bytes per record before allocator overhead),
the additional fixed 64 KiB writable image buffer, bytewise/no-locale ordering,
LF normalization, collapsed
failure status, no stderr diagnostics, and process-exit heap adoption. Each must
be classified as an explicit minimal-product choice or a reasonable replaceable
implementation—not retained merely because it shortens a proof. No arbitrary
cap, unstable algorithm, quadratic compare/copy path, weakened hardening, or
discarded partial-output fact is acceptable as proof convenience.

The single-root sequential process plan is canonical generated scaffolding, not
a second product artifact. Review its adapter theorem once as library authority,
not anew for every sort program. A parallel sorter, fused input/indexer, or
external merge plan is welcome only when its own
`ProcessPlanRealizes spec` proof preserves stable occurrence identity, failure
silence, committed-prefix behavior, and progress. A different weave is not
accepted merely because the same sample files happen to sort.

Any success is an interface failure. After libraries exist, the spike also needs
transitive axiom audit, writer/parser tests, instruction and decoder fuzzing,
Win32 API/heap probes, stable-sort differential/property tests, PE inspection,
and execution on reviewed Intel and AMD Windows hosts. Tests challenge the model;
they do not establish the proof.

## 11. Required source anchors

In addition to Spike 1's x86, Win64 ABI, PE, loader, `GetStdHandle`, `WriteFile`,
and `ExitProcess` anchors, implementation requires declaration-level citations
for `ReadFile`, `GetProcessHeap`, `HeapAlloc`, and `HeapReAlloc`, including
partial/zero reads, EOF distinctions, output parameters, blocking/overlapped
behavior, allocator failure, alignment, reallocation failure ownership, and
process teardown. Pure byte ordering, LF parsing, vector representation, stable
permutation, and mergesort laws are owned by Grass documents and Lean proofs and
must be listed in the source register with their theorem owners.


## Exact authored source snapshot

This snapshot is the exact comment-free source maintained under
`Spikes/2_Sort/`. Run `./check-spike-sources.ps1 -Spike 2` to check the
normalized cross-view equality and block classifications.

### `Assembly.lean`

<!-- grass-block: authored file=Assembly.lean -->
```lean
import Grass.Assembly.X86
import Grass.Platform.Win10.X64
import Grass.Std.Sort.Stable
import Spikes.«2_Sort».Spec

namespace Grass.Spikes.Sort

def policy : TargetOutcomeProjection SortOutcome UInt32 :=
  .successOrFailure
    (success := .success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

def stableSortContract : ComponentContract :=
  StableSort.contract format order

def stableSortModel : ImplementationModel :=
  StableSort.bottomUpMergeModel format order

theorem stableSortModelCorrect :
    ImplementationRealizesContract stableSortModel stableSortContract :=
  StableSort.bottomUpMergeCorrect format order

def plan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StandardByteSort projection

def sortStaticObjects : StaticObjectTable := static_objects {
  rodata align 1 {
    lf_byte: bytes #[10]
  }
  bss align 64 {
    output_buffer: zero 65536
  }
}

structure PhysicalLineDesc where
  offset : UInt64
  length : UInt64

def LineDesc : StructLayout Win64 := StructLayout.derive PhysicalLineDesc

structure SortFrameLayout where
  shadow : Bytes 32
  arg5 : UInt64
  ioCount : UInt32
  ioRequest : UInt32
  stdin : UInt64
  stdout : UInt64
  lines : UInt64
  scratch : UInt64
  lineCount : UInt64
  width : UInt64
  left : UInt64
  mid : UInt64
  right : UInt64
  i : UInt64
  j : UInt64
  k : UInt64
  appendPtr : UInt64
  appendRemaining : UInt64
  outputIndex : UInt64
  finalDescriptors : UInt64
  outUsed : UInt64
  savedRsi : UInt64
  savedRdi : UInt64
  flushPtr : UInt64
  flushRemaining : UInt64

def SortFrame : FrameLayout Win64 := FrameLayout.derive SortFrameLayout

def compareRecords (left right : AddressOperand) :
    VerifiedFragment (CompareEntry left right) CompareExit := asm_fragment {
    mov  rax, qword ptr [left + LineDesc.offset]
    add  rax, r13
    mov  r10, qword ptr [left + LineDesc.length]
    mov  rcx, qword ptr [right + LineDesc.offset]
    add  rcx, r13
    mov  r11, qword ptr [right + LineDesc.length]
    xor  r9d, r9d
.compare_loop:
    cmp  r9, r10
    jae  .left_end
    cmp  r9, r11
    jae  .less
    movzx edx, byte ptr [rax+r9]
    movzx r8d, byte ptr [rcx+r9]
    cmp  edx, r8d
    jb   .less
    ja   .greater
    add  r9, 1
    jmp  .compare_loop
.left_end:
    cmp  r9, r11
    jb   .less
    xor  eax, eax
    jmp  .done
.less:
    mov  eax, -1
    jmp  .done
.greater:
    mov  eax, 1
.done:
}

def flushOutput :
    VerifiedFragment FlushOutputEntry FlushOutputExit := asm_fragment {
    lea  rax, [rip + output_buffer]
    mov  qword ptr [rsp+SortFrame.flushPtr], rax
    mov  rax, qword ptr [rsp+SortFrame.outUsed]
    mov  qword ptr [rsp+SortFrame.flushRemaining], rax
.flush_head:
    cmp  qword ptr [rsp+SortFrame.flushRemaining], 0
    je   .flush_complete
    mov  eax, dword ptr [rsp+SortFrame.flushRemaining]
    mov  dword ptr [rsp+SortFrame.ioRequest], eax
    mov  rcx, qword ptr [rsp+SortFrame.stdout]
    mov  rdx, qword ptr [rsp+SortFrame.flushPtr]
    mov  r8d, dword ptr [rsp+SortFrame.ioRequest]
    lea  r9, [rsp+SortFrame.ioCount]
    mov  dword ptr [rsp+SortFrame.ioCount], 0
    mov  qword ptr [rsp+SortFrame.arg5], 0
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   .flush_failed
    mov  eax, dword ptr [rsp+SortFrame.ioCount]
    cmp  eax, dword ptr [rsp+SortFrame.ioRequest]
    ja   provider_violation
    test eax, eax
    jz   .flush_stalled
    add  qword ptr [rsp+SortFrame.flushPtr], rax
    sub  qword ptr [rsp+SortFrame.flushRemaining], rax
    jmp  .flush_head
.flush_complete:
    mov  qword ptr [rsp+SortFrame.outUsed], 0
    xor  eax, eax
    jmp  .flush_done
.flush_failed:
    mov  eax, 1
    jmp  .flush_done
.flush_stalled:
    mov  eax, 2
.flush_done:
}

def bufferAppend (pointer length : MachineOperand) :
    VerifiedFragment (BufferAppendEntry pointer length) BufferAppendExit := asm_fragment {
    mov  qword ptr [rsp+SortFrame.savedRsi], rsi
    mov  qword ptr [rsp+SortFrame.savedRdi], rdi
    mov  qword ptr [rsp+SortFrame.appendPtr], pointer
    mov  qword ptr [rsp+SortFrame.appendRemaining], length
.append_head:
    cmp  qword ptr [rsp+SortFrame.appendRemaining], 0
    je   .append_complete
    cmp  qword ptr [rsp+SortFrame.outUsed], 65536
    jb   .append_have_room
    $(flushOutput)
    test eax, eax
    jnz  .append_restore
    jmp  .append_head
.append_have_room:
    mov  rcx, 65536
    sub  rcx, qword ptr [rsp+SortFrame.outUsed]
    mov  rax, qword ptr [rsp+SortFrame.appendRemaining]
    cmp  rax, rcx
    cmovb rcx, rax
    mov  r10, rcx
    mov  rsi, qword ptr [rsp+SortFrame.appendPtr]
    lea  rdi, [rip + output_buffer]
    add  rdi, qword ptr [rsp+SortFrame.outUsed]
    cld
    rep movsb
    mov  qword ptr [rsp+SortFrame.appendPtr], rsi
    sub  qword ptr [rsp+SortFrame.appendRemaining], r10
    add  qword ptr [rsp+SortFrame.outUsed], r10
    jmp  .append_head
.append_complete:
    xor  eax, eax
.append_restore:
    mov  rsi, qword ptr [rsp+SortFrame.savedRsi]
    mov  rdi, qword ptr [rsp+SortFrame.savedRdi]
}

def failureExit (outcome : SortOutcome) :
    VerifiedFragment (FailureExitEntry outcome) NoReturn := asm_fragment {
    mov  ecx, policy.status outcome
    jmp  exit
}

def sortConstructorClosure : FragmentConstructorClosure plan := constructors {
  compareRecords
  flushOutput
  bufferAppend
  failureExit
}

def sortSource : AsmSource plan :=
  asm_source
    (statics := sortStaticObjects)
    (constructors := sortConstructorClosure) {

entry:
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, SortFrame.size
    call qword ptr [rip + __imp_GetProcessHeap]
    test rax, rax
    jz   resource_exhausted
    mov  r12, rax
    mov  ecx, STD_INPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdin_unavailable
    cmp  rax, INVALID_HANDLE_VALUE
    je   stdin_unavailable
    mov  qword ptr [rsp+SortFrame.stdin], rax
    xor  r13d, r13d
    xor  r14d, r14d
    xor  r15d, r15d
    jmp  read_head

read_head: @placement [input := r13, length := r14, capacity := r15]
           @invariant growable_input_vec
           @frontier_or_measure(read_or_growth)
    cmp  r14, r15
    je   grow_input
read_issue:

    mov  rax, r15
    sub  rax, r14
    mov  r8d, 0xffffffff
    cmp  rax, r8
    cmovb r8, rax
    test r8d, r8d
    jz   grow_input
    mov  dword ptr [rsp+SortFrame.ioRequest], r8d
    mov  rcx, qword ptr [rsp+SortFrame.stdin]
    lea  rdx, [r13+r14]
    lea  r9, [rsp+SortFrame.ioCount]
    mov  dword ptr [rsp+SortFrame.ioCount], 0
    mov  qword ptr [rsp+SortFrame.arg5], 0
    call qword ptr [rip + __imp_ReadFile]
    test eax, eax
    jz   read_failed
    mov  eax, dword ptr [rsp+SortFrame.ioCount]
    cmp  eax, dword ptr [rsp+SortFrame.ioRequest]
    ja   provider_violation @violation_edge(.excessReadCount)
    test eax, eax
    jz   input_eof
    add  r14, rax
    jmp  read_head

grow_input: @placement [input := r13, length := r14, capacity := r15]
            @invariant growable_input_vec
            @measure representable_capacity_remaining
    test r15, r15
    jnz  grow_existing
    mov  ebx, 4096
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  r13, rax
    mov  r15, rbx
    jmp  read_issue

grow_existing:
    mov  rbx, -1
    shr  rbx, 1
    cmp  r15, rbx
    ja   grow_saturate
    mov  rbx, r15
    shl  rbx, 1
    jmp  grow_realloc
grow_saturate:
    mov  rbx, -1
    cmp  r15, rbx
    je   resource_exhausted
grow_realloc:
    mov  rcx, r12
    xor  edx, edx
    mov  r8, r13
    mov  r9, rbx
    call qword ptr [rip + __imp_HeapReAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  r13, rax
    mov  r15, rbx
    jmp  read_issue

input_eof:
    xor  ebp, ebp
    xor  ebx, ebx
    test r14, r14
    jz   no_descriptors
count_loop: @placement [input := r13, inputLength := r14,
                        cursor := rbx, lineCount := rbp]
            @invariant count_lf_prefix
            @measure r14-rbx
    cmp  rbx, r14
    jae  count_suffix
    cmp  byte ptr [r13+rbx], 10
    jne  count_next
    add  rbp, 1
    jc   resource_exhausted
count_next:
    add  rbx, 1
    jc   resource_exhausted
    jmp  count_loop
count_suffix:
    lea  rax, [r14-1]
    cmp  byte ptr [r13+rax], 10
    je   allocate_descriptors
    add  rbp, 1
    jc   resource_exhausted

allocate_descriptors:
    mov  rbx, rbp
    shl  rbx, 4
    mov  rax, rbx
    shr  rax, 4
    cmp  rax, rbp
    jne  resource_exhausted
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  rdi, rax
    mov  qword ptr [rsp+SortFrame.lines], rax
    mov  rcx, r12
    xor  edx, edx
    mov  r8, rbx
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted
    mov  rsi, rax
    mov  qword ptr [rsp+SortFrame.scratch], rax
    jmp  descriptor_scan_init

no_descriptors:
    xor  edi, edi
    xor  esi, esi
    mov  qword ptr [rsp+SortFrame.lines], 0
    mov  qword ptr [rsp+SortFrame.scratch], 0
    mov  qword ptr [rsp+SortFrame.lineCount], 0
    mov  qword ptr [rsp+SortFrame.finalDescriptors], 0
    jmp  sort_done

descriptor_scan_init:
    mov  qword ptr [rsp+SortFrame.lineCount], rbp
    xor  r8d, r8d
    xor  r9d, r9d
    xor  r10d, r10d
descriptor_scan: @placement [cursor := r8, lineStart := r9, index := r10]
                 @invariant represents_scanned_prefix
                 @measure r14-r8
    cmp  r8, r14
    jae  descriptor_suffix
    cmp  byte ptr [r13+r8], 10
    jne  descriptor_next_byte
    mov  rax, r10
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  qword ptr [rdx + LineDesc.offset], r9
    mov  rcx, r8
    sub  rcx, r9
    mov  qword ptr [rdx + LineDesc.length], rcx
    add  r10, 1
    add  r8, 1
    mov  r9, r8
    jmp  descriptor_scan
descriptor_next_byte:
    add  r8, 1
    jmp  descriptor_scan
descriptor_suffix:
    cmp  r9, r14
    jae  descriptor_scan_done
    mov  rax, r10
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  qword ptr [rdx + LineDesc.offset], r9
    mov  rcx, r14
    sub  rcx, r9
    mov  qword ptr [rdx + LineDesc.length], rcx
    add  r10, 1
descriptor_scan_done:
    cmp  r10, rbp
    jne  internal_fault
    mov  qword ptr [rsp+SortFrame.width], 1
    jmp  sort_pass

sort_pass: @contract StableSortContract
           @invariant stable_merge_pass(input, lines, scratch)
           @measure merge_pass_measure
    mov  rax, qword ptr [rsp+SortFrame.width]
    cmp  rax, rbp
    jae  sort_complete
    mov  qword ptr [rsp+SortFrame.left], 0
merge_run_head:
    mov  rax, qword ptr [rsp+SortFrame.left]
    cmp  rax, rbp
    jae  merge_pass_done
    mov  rcx, rax
    add  rcx, qword ptr [rsp+SortFrame.width]
    cmp  rcx, rbp
    cmova rcx, rbp
    mov  qword ptr [rsp+SortFrame.mid], rcx
    mov  rdx, rcx
    add  rdx, qword ptr [rsp+SortFrame.width]
    cmp  rdx, rbp
    cmova rdx, rbp
    mov  qword ptr [rsp+SortFrame.right], rdx
    mov  qword ptr [rsp+SortFrame.i], rax
    mov  qword ptr [rsp+SortFrame.j], rcx
    mov  qword ptr [rsp+SortFrame.k], rax
merge_choose: @invariant stable_merge_cursors(i,j,k)
              @measure (mid-i)+(right-j)
    mov  rax, qword ptr [rsp+SortFrame.i]
    cmp  rax, qword ptr [rsp+SortFrame.mid]
    jae  merge_drain_right
    mov  rcx, qword ptr [rsp+SortFrame.j]
    cmp  rcx, qword ptr [rsp+SortFrame.right]
    jae  merge_drain_left
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  rax, rcx
    shl  rax, 4
    lea  r8, [rdi+rax]
    $(compareRecords rdx r8)
    cmp  eax, 0
    jle  merge_take_left
merge_take_right:
    mov  rax, qword ptr [rsp+SortFrame.j]
    add  qword ptr [rsp+SortFrame.j], 1
    jmp  merge_copy
merge_take_left:
    mov  rax, qword ptr [rsp+SortFrame.i]
    add  qword ptr [rsp+SortFrame.i], 1
merge_copy:
    shl  rax, 4
    lea  rdx, [rdi+rax]
    mov  rax, qword ptr [rsp+SortFrame.k]
    shl  rax, 4
    lea  r8, [rsi+rax]
    mov  rcx, qword ptr [rdx + LineDesc.offset]
    mov  qword ptr [r8 + LineDesc.offset], rcx
    mov  rcx, qword ptr [rdx + LineDesc.length]
    mov  qword ptr [r8 + LineDesc.length], rcx
    add  qword ptr [rsp+SortFrame.k], 1
    jmp  merge_choose
merge_drain_left:
    mov  rax, qword ptr [rsp+SortFrame.i]
    cmp  rax, qword ptr [rsp+SortFrame.mid]
    jae  merge_run_done
    add  qword ptr [rsp+SortFrame.i], 1
    jmp  merge_copy
merge_drain_right:
    mov  rax, qword ptr [rsp+SortFrame.j]
    cmp  rax, qword ptr [rsp+SortFrame.right]
    jae  merge_run_done
    add  qword ptr [rsp+SortFrame.j], 1
    jmp  merge_copy
merge_run_done:
    mov  rax, qword ptr [rsp+SortFrame.right]
    mov  qword ptr [rsp+SortFrame.left], rax
    jmp  merge_run_head
merge_pass_done:
    xchg rdi, rsi
    mov  rax, qword ptr [rsp+SortFrame.width]
    add  rax, rax
    cmp  rax, rbp
    cmova rax, rbp
    mov  qword ptr [rsp+SortFrame.width], rax
    jmp  sort_pass
sort_complete:
    mov  qword ptr [rsp+SortFrame.finalDescriptors], rdi

sort_done:
    mov  ecx, STD_OUTPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdout_unavailable
    cmp  rax, INVALID_HANDLE_VALUE
    je   stdout_unavailable
    mov  qword ptr [rsp+SortFrame.stdout], rax

    mov  qword ptr [rsp+SortFrame.outputIndex], 0
    mov  qword ptr [rsp+SortFrame.outUsed], 0
    jmp  emit_head

emit_head: @invariant sorted_occurrence_consumer(finalDescriptors)
           @invariant buffered_stdout(output_buffer, outUsed, committedPrefix)
           @measure remaining_source_bytes_plus_records
    mov  rax, qword ptr [rsp+SortFrame.outputIndex]
    cmp  rax, rbp
    jae  emit_final_flush
    shl  rax, 4
    add  rax, qword ptr [rsp+SortFrame.finalDescriptors]
    mov  rdx, qword ptr [rax + LineDesc.offset]
    add  rdx, r13
    mov  r8, qword ptr [rax + LineDesc.length]
    $(bufferAppend rdx r8)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    lea  rdx, [rip + lf_byte]
    mov  r8d, 1
    $(bufferAppend rdx r8)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    add  qword ptr [rsp+SortFrame.outputIndex], 1
    jmp  emit_head

emit_final_flush:
    $(flushOutput)
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    jmp  exit_success

stdin_unavailable:   @terminal(.inputFailure) @audit(.stdinUnavailable)
    $(failureExit .inputFailure)
read_failed:         @terminal(.inputFailure) @audit(.readFailed)
    $(failureExit .inputFailure)
resource_exhausted:  @terminal(.allocationFailure) @audit(.resourceExhausted)
    $(failureExit .allocationFailure)
stdout_unavailable:  @terminal(.outputFailure) @audit(.stdoutUnavailable)
    $(failureExit .outputFailure)
write_failed:        @terminal(.outputFailure) @audit(.writeFailed)
    $(failureExit .outputFailure)
no_progress:         @terminal(.outputFailure) @audit(.noProgress)
    $(failureExit .outputFailure)
exit_success:       @terminal(.success)
    xor ecx, ecx
exit:
    call qword ptr [rip + __imp_ExitProcess]
    ud2 @containment_tail(.terminalUnexpectedReturn)
provider_violation:
    ud2 @containment_tail(.returnedCountExceedsRequest)
internal_fault:
    ud2 @containment_tail(.provedUnreachable)

}

end Grass.Spikes.Sort
```

### `Program.lean`

<!-- grass-block: authored file=Program.lean -->
```lean
import Grass.Emit
import Spikes.«2_Sort».Assembly

namespace Grass.Spikes.Sort

def parserWitness :
    SelectedProcessRequirementWitness (lineParserRequirement resources) :=
  Format.inlineParserWitness
    (format := lineStreamFormat)
    (source := sortSource)

def sortVerified : VerifiedProgram spec := by
  verify_assembly plan
    using_requirement parserWitness
    using_model stableSortModelCorrect
    with sortSource

def bytes : ByteArray := emitProgram sortVerified

end Grass.Spikes.Sort
```

### `Spec.lean`

<!-- grass-block: authored file=Spec.lean -->
```lean
import Grass.Spec.Console
import Grass.Spec.Grammar
import Grass.Spec.Resource

namespace Grass.Spikes.Sort

def resources : ConsoleBufferResourceModel :=
  ConsoleBufferResourceModel.untilMemoryExhaustion
    (onExhaustion := .terminateWithNoOutput)
    (capacity := .noArtificialLimit)

def format : ByteLineFormat := .lfDelimited (.normalizeFinal true)

def order : ByteStringOrder := .lexicographicUnsigned

inductive SortOutcome
  | success
  | allocationFailure
  | inputFailure
  | outputFailure

structure Occurrence where
  ordinal : Nat
  value : ByteArray

def Occurrence.le (left right : Occurrence) : Prop :=
  order.le left.value right.value

def stableSorted (input output : Vec Occurrence) : Prop :=
  output.Permutation input ∧
  output.Pairwise Occurrence.le ∧
  ∀ i j, i < j -> input[i].value = input[j].value ->
    (output.findIdx? input[i]).get! < (output.findIdx? input[j]).get!

def lineStreamFormat : Format (Vec ByteArray) :=
  Console.byteLineStreamFormat format

def lineParserRequirement {R : Type} [ResourceModel R]
    (resources : R) : ProcessRequirement resources :=
  Format.parserRequirement lineStreamFormat

def sortSuite {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : SpecificationSuite resources :=
  Console.stableLineSortSuite
    (resources := resources)
    (format := format)
    (order := order)
    (outcomes := SortOutcome)
    (parser := lineParserRequirement resources)

def sortSpec {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (sortSuite resources)
    |>.onResourceExhaustion .allocationFailure
    |>.withLiveness
        (.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem sortSpecCorrect {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) : MeetsAllSpecificationTheorems (sortSpec resources) :=
  Console.stableLineSortSuiteCaptureCorrect resources format order SortOutcome
    (lineParserRequirement resources)

theorem successfulTraceIffStableSorted
    {R : Type} [ResourceModel R] [BufferedSortResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (sortSpec resources) input output ↔
      StableFormattedOccurrenceOutput format input output stableSorted :=
  Console.stableLineSortContract_success_iff
    resources format order SortOutcome

def spec : SpecProcess resources := sortSpec resources

end Grass.Spikes.Sort
```
