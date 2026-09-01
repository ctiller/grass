# Spike 3: bounded-memory streaming gzip to Win32 PE

Status: design artifact for adversarial review; intentionally not compilable.

Authoring view: agents maintain exactly `Spec.lean`, `Assembly.lean`, and
`Program.lean`. The exact snapshot is at the end of this document. Source
closure, component binding, and artifact records shown below are generated
review projections rather than additional authored modules.

This document proposes the complete proof shape before its supporting Lean
libraries exist. Normative force remains with the owning documents linked from
[README.md](README.md). The resource-parameterized root `SpecProcess`, including
its grammar/round-trip/streaming/failure components and junctions, is the only
precious semantic artifact. Process presentations and selected child witnesses
are reviewed, versioned, replaceable proof inputs. The selected process weave,
fixed-block policy, hash-chain compressor, literal assembly, and Win32 plan are
reviewed replaceable construction inputs. Certificates, layout, and bytes are
derived.

This spike deliberately reaches raw assembly. Every algorithmic helper and
error path appears below as instructions. A contract explains why a displayed
body is correct; it never replaces the body.

## 1. Application surface

```lean
namespace Grass.Spike3

/-!
`spec` says only what makes this a gzip compressor: on successful finite input,
stdout is exactly one well-formed gzip member whose decoded payload is the exact
input. It does not canonize an implementation's block split, search heuristic,
header metadata, or compression ratio.

Before-output setup failure is silent. Once streaming emission begins, an I/O
failure may expose only a prefix justified by the compressor construction trace.
Infinite input is productive rather than terminating. Safety is unconditional.
-/
inductive GzipOutcome
  | success | allocationFailure | inputFailure | outputFailure

def resources : StreamingResourceModel :=
  StreamingResourceModel.console
    |>.withResidentMemory .boundedIndependentOfInputLength

def gzipMemberFormat : Format Gzip.Member :=
  Gzip.memberFormat

def gzipSuite {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : SpecificationSuite resources :=
  Console.streamingGzipSuite
    (resources := resources)
    (members := .one) (outputFormat := gzipMemberFormat)
    (failureOutput := .constructionPrefix)

def gzipSpec {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (gzipSuite resources)
    |>.withOutcomes GzipOutcome
    |>.withProgress
        (.reactiveBetweenFrontiers
          |>.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem gzipSpecCorrect {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : MeetsAllSpecificationTheorems (gzipSpec resources) :=
  Console.streamingGzipSuiteCaptureCorrect
    resources GzipOutcome gzipMemberFormat

theorem successfulTraceIffOneMemberRoundTrip
    {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (gzipSpec resources) input output ↔
      Gzip.IsExactlyOneMember output ∧ Gzip.inflate output = .ok input :=
  Console.streamingGzipContract_success_iff resources GzipOutcome

def spec : SpecProcess resources := gzipSpec resources

def policy : TargetOutcomeProjection GzipOutcome UInt32 :=
  .successOrFailure
    (success := GzipOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

/-!
Algorithmic tuning is reviewed assembly-module data, never a platform type.
Changing probes, matcher organization, block choice, or instruction scheduling
does not change Win32/ABI/ISA provider identity.
-/
def codecPlan : GzipImplementationPlan :=
  .fixed32KHashChain (maxProbes := 64)

def platformPlan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StreamingIO projection

def gzipVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    with gzipSource

def bytes : ByteArray := emitProgram gzipVerified

end Grass.Spike3
```

The application author maintains one minimal behavioral declaration and policy,
one local `codecPlan`, the platform selection, and authored assembly. Codec
lemmas may be reused by another ISA, another process weave, or a generated
implementation without making this source a semantic oracle.

### 1.1 Synthesized sequential process realization

```lean
def gzipProcessRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)

theorem gzipProcessPlanRealizes :
    ProcessPlanRealizes spec gzipProcessRealization.plan :=
  gzipProcessRealization.correct
```

The normalized plan has one stateful root, standard asynchronous byte-ingress
and byte-egress children, and fresh occurrence-indexed children for
input/output acquisition, arena acquisition, provider operations, and terminal
status. Each positive partial read becomes an exact ingress chunk; the codec is
proved invariant under all rechunkings of the same byte stream. Each positive
partial write commits one exact prefix while the egress process retains the
unique suffix. The standard adapter supplies their nominal protocol keys, exhaustive
lifecycle cases, Hoare escrows, non-vacuous initial network, child-choice
completeness, and global progress. The author writes none of that graph.

The closed registry is the shortest surface, not the only economical surface.
A novel gzip header, extra compression pass, retry rule, or failure policy over
the same typed effects is a `SequentialMachine`: the author supplies its state,
decision function, invariant, semantic refinement, and progress. The adapter
derives the unique outstanding occurrence, dependent continuation, pending
equation, and child binding by induction over the decision syntax. Only a
deliberately multi-effect relational transition selects the lower-level
`DirectRelationalProgram` interface and its explicit bag equation. This is a
required mutation fixture for Spike 3: adding a custom header must not force an
explicit process graph or handwritten occurrence algebra.

The reusable zlib component is a stateful relational transducer, not a platform
plan and not automatically a concurrent actor. Its interface consumes each
input occurrence once and returns construction bytes plus exact decoded-prefix,
CRC/ISIZE, and finality relations. `codecPlan` selects its fixed-Huffman/hash-
chain realization locally. An explicit plan may later split CRC, LZ77, Huffman,
and bit writing into bounded pipeline processes without changing `spec` or the
stable driver boundary.

Fractally, `Std.Zlib` may prove that transducer by composing CRC, LZ77, block,
Huffman, and bit-writer subprocesses, then applying `flatten_correct` and a
`SerializablePlan` theorem. The present assembly executes one ordinary serial
codec loop; no actor queues or scheduler are implied by the library's internal
proof graph. A genuinely parallel codec can instead retain the explicit plan.

The reusable algorithm adjacency is explicit:

```lean
def fixed32KModel : ImplementationModel := Std.Zlib.Fixed32K.model codecPlan

theorem fixed32KModel_correct :
  ImplementationRealizesContract fixed32KModel
    (Deflate.Fixed32KContract codecPlan)

theorem gzipSource_refines_model :
  AssemblyRefinesImplementation
    codecAlgorithmScope fixed32KRepresentation fixed32KModel

theorem fixed32K_contract_connects :
  ComponentContractRefinesRequirement
    (Deflate.Fixed32KContract codecPlan) gzipCodecRequirement
```

The model theorem owns CRC, LZ77, fixed-Huffman, bitstream, round-trip, and
construction-prefix mathematics once. The assembly theorem owns the exact codec
arena/layout representation and loops inside `codecAlgorithmScope`. Partial I/O,
application failure/progress, and terminal behavior remain separate requirements
composed through `fixed32K_contract_connects`; the codec model does not claim the
whole console application. The exact authored instructions simulate the selected
component.

The `@implements fixed32KContract using fixed32KModelCorrect` annotation causes
the elaborator to derive a reported
`gzipImplementationBinding : ImplementationBinding gzipExpandedSource
gzipCodecRequirement`. Its fields name the codec source scope, physical state
representation, banked `fixed32KModelCorrect` certificate,
`gzipSourceRefinesModel`, and `fixed32KContractConnects`. Whole-driver
verification consumes that value; it does not repeat codec mathematics. The
generated binding-mutation fixture requires a codec-body or arena
edit to stop at assembly refinement and a model-contract edit to stop at the
component junction.

The adapter proof instantiates standard theorems for read fragmentation,
construction-prefix composition, the pre-output arena barrier, bounded live
state, partial commits, terminal projection, cancellation/disposition, coupled
execution, and progress between API frontiers. Section 6 supplies the complete
assembly realizing the resulting universal process plan.

## 2. Portable observations and nondeterminism

```lean
inductive GzipOutcome
  | success
  | stdinUnavailable | stdoutUnavailable | resourceExhausted
  | readFailed | writeFailed | noProgress

structure GzipObservation where
  inputTrace  : ByteArray
  stdoutTrace : ByteArray
  outcome     : GzipOutcome
  status      : UInt32

def GzipObservation.Accepts (o : GzipObservation) : Prop :=
  o.status = policy.status o.outcome ∧
  match o.outcome with
  | .success =>
      ∃ member,
        Gzip.parseAll o.stdoutTrace = .ok [member] ∧
        member.payload = o.inputTrace
  | .stdinUnavailable | .stdoutUnavailable | .resourceExhausted =>
      o.stdoutTrace = #[]
  | .readFailed | .writeFailed | .noProgress =>
      ∃ construction,
        ValidGzipConstructionPrefix o.inputTrace construction o.stdoutTrace
```

`ValidGzipConstructionPrefix` is not `True` and is not merely byte-prefixhood of
an archive chosen after the fact. It contains the exact compressor state reached
after the observed input prefix: header state, completed fixed blocks, current
token prefix, bit accumulator, CRC/ISIZE state, and write cursor. Extending that
state with any permitted future input and successful provider choices produces a
well-formed member beginning with the observed stdout bytes. It therefore rules
out invented bytes while honestly admitting an incomplete final block/trailer.

The theorem quantifies over every finite or infinite input history, every legal
`ReadFile` fragmentation, failure/EOF point, every partial `WriteFile` result,
allocator address/failure, admissible load base/import environment, interrupt,
fault, and responsive or nonresponsive branching strategy. A native round trip
is a probe, never proof. Under eventual EOF and universal responsive continuations
the program terminates. Without EOF it performs finite internal work between
frontiers and, when output remains responsive, exposes unbounded input capacity
while retaining a fixed live heap footprint.

## 3. The reusable `Std.Zlib` boundary

The spike demands these standard-library interfaces rather than defining a
spike-private codec:

```lean
namespace Grass.Std.Zlib

structure GzipMember where
  payload : ByteArray
  metadata : GzipMetadata

def Deflate.parse : ByteArray -> Except DeflateError (ByteArray × ByteArray)
def Zlib.parse : ByteArray -> Except ZlibError (ByteArray × ByteArray)
def Zlib.write : ByteArray -> ByteArray
def Gzip.parseMember : ByteArray -> Except GzipError (GzipMember × ByteArray)
def Gzip.parseAll : ByteArray -> Except GzipError (Vec GzipMember)
def Gzip.writeMember : GzipMember -> ByteArray

theorem gzip_writer_round_trip (m : GzipMember) :
  Gzip.parseMember (Gzip.writeMember m) = .ok (m, #[])

theorem gzip_parser_correct {bytes m rest} :
  Gzip.parseMember bytes = .ok (m, rest) ->
  RFC1952.MemberEncoding bytes m rest

theorem gzip_success_canonicalizes {bytes members} :
  Gzip.parseAll bytes = .ok members ->
  Gzip.parseAll (members.flatMap Gzip.writeMember) = .ok members

theorem zlib_writer_round_trip (payload : ByteArray) :
  Zlib.parse (Zlib.write payload) = .ok (payload, #[])

end Grass.Std.Zlib
```

The reader is total and rejects malformed/reserved flags, truncated optional
fields, malformed stored/fixed/dynamic DEFLATE, impossible Huffman trees,
distance-before-history, CRC mismatch, ISIZE mismatch, and disallowed trailing
data. It parses FEXTRA/FNAME/FCOMMENT/FHCRC, all three legal DEFLATE block kinds,
and concatenated members. The canonical writer may normalize metadata; its
value round trip is exact even where byte round trip is intentionally not.
`Std.Zlib` also owns Adler-32 and the RFC 1950 wrapper; gzip owns CRC-32 and the
RFC 1952 wrapper. Both reuse the same DEFLATE bitstream, Huffman, and LZ77
definitions rather than growing two codec stacks.

The selected construction uses a narrower reusable theorem:

```lean
def Fixed32K.write (input : ByteArray) : ByteArray

theorem fixed32k_round_trip (input : ByteArray) :
  Gzip.parseAll (Fixed32K.write input) =
    .ok [{ payload := input, metadata := deterministicMetadata }]

theorem fixed32k_prefix (s : Fixed32K.State) :
  s.Invariant -> ValidGzipConstructionPrefix s.input s s.written
```

Its proof factors into LZ77 expansion, fixed canonical-code inversion, bit-writer
and bit-reader correspondence, block concatenation, CRC-32, and member framing.
The useful gasm facts are the universally quantified LZ77 expansion and
fixed-block round trip. Gasm's pointwise `native_decide` container checks and its
unproved dynamic-Huffman branch are explicitly not imported as assurance.

`findMatch` is a heuristic. Correctness needs only a certificate for each chosen
reference; changing chain depth or choosing all literals changes size and speed,
not the portable theorem. Compression-ratio and throughput regressions are
product gates, not kernel propositions masquerading as semantic correctness.

## 4. Physical state, provenance, and obligations

One 295,168-byte process-heap allocation is divided by a proved layout:

```lean
structure GzipMachineState where
  heap       : UInt64 -- 0
  stdin      : UInt64 -- 8
  stdout     : UInt64 -- 16
  inputLen   : UInt32 -- 24
  position   : UInt32 -- 28
  outLen     : UInt32 -- 32
  bitCount   : UInt32 -- 36
  bitAcc     : UInt64 -- 40
  crc        : UInt32 -- 48, preconditioned
  isize      : UInt32 -- 52, modular
  root       : UInt64 -- 56
  input      : UInt64 -- 64
  heads      : UInt64 -- 72
  previous   : UInt64 -- 80
  output     : UInt64 -- 88
  requested  : UInt32 -- 96
  transferred : UInt32 -- 100

def gzipLayout : ArenaLayout :=
  .exact 295168 [
    .object `state    0      256      16,
    .object `input    256    32768    16,
    .array  `heads    33024  UInt16   65536,
    .array  `previous 164096 UInt16   32768,
    .object `output   229632 65536    16]
```

The single upstream allocation creates five child provenances. They do not
alias, even though one root cleanup obligation covers them. `input[0..inputLen)`
is initialized and immutable during compression. `heads` is initialized to
`0xffff` at every block start. `previous[p]` becomes initialized exactly when
position `p` is inserted. A head/link value other than `0xffff` is proved less
than the current position and names the current block generation. Thus stale
indices cannot cross reset even though numerical offsets repeat.

The bit writer owns `output[0..outLen)` initialized and
`output[outLen..65536)` writable. A `WriteFile` call lends only the requested
initialized residual slice plus the four-byte result slot. A conforming return
returns the same loan identities and advances only by its dependent byte count.
The input call symmetrically lends only uninitialized spare input bytes and
initializes exactly the completed prefix.

All allocation and handle validation precedes creation of the first output byte
in the abstract effect trace. After emission begins no allocation can fail.
Terminal `ExitProcess` transfers the root heap obligation to the cited process
teardown disposition. Standard handles are borrowed, never closed or adopted.
General environment violation ends assurance at its first event; the two
displayed excess-count edges use occurrence-indexed affine return envelopes only
to reach the minimal containment tail.

## 5. Selected compression algorithm

The executable emits one deterministic header:

```text
1f 8b 08 00  00 00 00 00  00 ff
ID1 ID2 CM FLG   MTIME      XFL OS(unknown)
```

Input is accumulated to 32 KiB. A full block is emitted non-final; at EOF a
partial block is emitted final, or an empty final fixed block follows an exact
multiple of 32 KiB. Every block resets the dictionary. The three-byte hash is
`((b0 * 251 + b1) * 251 + b2) & 0xffff`. Each bucket and predecessor is a
`UInt16` offset; `0xffff` is the sentinel. Search visits at most 64 prior
candidates, chooses the longest valid match, and on equal length retains the
nearest previously visited candidate. Maximum distance is therefore 32,768 and
maximum length is 258. Positions consumed by a match are individually inserted.

The chosen block representation is fixed Huffman. This is fully conforming gzip
and has bounded predictable proof cost. Dynamic-Huffman emission is a later
replaceable codec plan, not something the portable spec forbids. The selected
artifact is expected to be useful as a streaming filter, but review must not
claim zlib-equivalent ratio or speed: its dictionary reset and 64-probe bound are
real product tradeoffs.

CRC-32 is updated over each successfully read byte with reversed polynomial
`0xedb88320`, initial state `0xffffffff`, and final complement. ISIZE accumulates
the same count modulo 2^32. The bit writer is LSB-first and retains at most seven
pending bits. Its 64 KiB output array is drained with a complete partial-write
loop.

## 6. Complete authored x86-64 CFG

The following is the intended `asm_source`. That command-level generator creates
stable, individually nameable source declarations for every displayed block; it
does not claim specification or platform refinement by itself. `@...` clauses
are erased proof annotations. `call_local` is a direct relative `call`; it is
printed distinctly only so review can distinguish internal Grass ABI calls from
IAT calls. Internal helpers preserve `r12` (the state pointer) and all Win64
nonvolatile registers; `eax = 0` means success, `eax = 1` write failure, `eax =
2` zero progress, and `eax = 3` excess-count provider violation. Every helper
body is present.

```text
def GzipFrame := stackLayout win64 {
  shadow : Bytes 32
  overlapped : UInt64
  transferred : UInt32
  locals : Bytes 28
}

def GzipArena := structLayout win64 {
  heap stdin stdout : UInt64
  inputLength position outputLength bitCount : UInt32
  bitAccumulator : UInt64
  crc totalInput : UInt32
  root input head prev output : UInt64
  ioRequest ioCount : UInt32
  reserved : Bytes 152
  inputBytes : Bytes 32768
  headEntries : Bytes 131072
  prevEntries : Bytes 65536
  outputBytes : Bytes 65536
}

def ProcessBlockFrame :=
  win64.callFrameAfterSaves #[rbx, rbp, rsi, rdi, r13, r14, r15]
def EmitReferenceFrame := win64.callFrameAfterSaves #[rbx, rsi, rdi]
def EmitFixedSymbolFrame := win64.callFrameAfterSaves #[]
def EmitBitsFrame := win64.callFrameAfterSaves #[rbx]
def EmitRawByteFrame := win64.callFrameAfterSaves #[rbx]
def FlushFrame := stackLayout win64 {
  shadow : Bytes 32
  overlapped : UInt64
  transferred : UInt32
}
def GzipHeader := packedLayout {
  magic : UInt16
  compressionMethod flags : UInt8
  modificationTime : UInt32
  extraFlags operatingSystem : UInt8
}

def gzipSource : AsmSource platformPlan := asm_source using codecPlan {

entry:
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, GzipFrame.size
    mov  ecx, STD_INPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdin_unavailable
    cmp  rax, -1
    je   stdin_unavailable
    mov  r13, rax
    mov  ecx, STD_OUTPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdout_unavailable
    cmp  rax, -1
    je   stdout_unavailable
    mov  r14, rax
    call qword ptr [rip + __imp_GetProcessHeap]
    test rax, rax
    jz   resource_exhausted_no_root
    mov  rbx, rax
    mov  rcx, rbx
    xor  edx, edx
    mov  r8d, GzipArena.size
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted_no_root
    mov  r12, rax
    mov  [r12 + GzipArena.heap], rbx
    mov  [r12 + GzipArena.stdin], r13
    mov  [r12 + GzipArena.stdout], r14
    mov  [r12 + GzipArena.root], r12
    lea  rax, [r12 + GzipArena.inputBytes]
    mov  [r12 + GzipArena.input], rax
    lea  rax, [r12 + GzipArena.headEntries]
    mov  [r12 + GzipArena.head], rax
    lea  rax, [r12 + GzipArena.prevEntries]
    mov  [r12 + GzipArena.prev], rax
    lea  rax, [r12 + GzipArena.outputBytes]
    mov  [r12 + GzipArena.output], rax
    mov  dword ptr [r12 + GzipArena.inputLength], 0
    mov  dword ptr [r12 + GzipArena.position], 0
    mov  dword ptr [r12 + GzipArena.outputLength], 10
    mov  dword ptr [r12 + GzipArena.bitCount], 0
    mov  qword ptr [r12 + GzipArena.bitAccumulator], 0
    mov  dword ptr [r12 + GzipArena.crc], 0xffffffff
    mov  dword ptr [r12 + GzipArena.totalInput], 0
    mov  rdi, [r12 + GzipArena.output]
    mov  rax, 0x0000000000088b1f
    mov  [rdi + GzipHeader.magic], rax
    mov  word ptr [rdi + GzipHeader.extraFlags], 0xff00
    jmp  read_head

read_head: @invariant collecting_block(state, capacity=32768)
           @frontier_or_measure(read_or_remaining_spare)
    mov  eax, [r12 + GzipArena.inputLength]
    cmp  eax, 32768
    je   process_nonfinal_block
    mov  ecx, 32768
    sub  ecx, eax
    mov  [r12 + GzipArena.ioRequest], ecx
    mov  rcx, [r12 + GzipArena.stdin]
    mov  rdx, [r12 + GzipArena.input]
    add  rdx, rax
    mov  r8d, [r12 + GzipArena.ioRequest]
    lea  r9, [rsp + GzipFrame.transferred]
    mov  dword ptr [rsp + GzipFrame.transferred], 0
    mov  qword ptr [rsp + GzipFrame.overlapped], 0
    call qword ptr [rip + __imp_ReadFile]
    test eax, eax
    jz   read_failed
    mov  eax, [rsp + GzipFrame.transferred]
    cmp  eax, [r12 + GzipArena.ioRequest]
    ja   read_count_violation @violation_edge(.excessReadCount)
    test eax, eax
    jz   input_eof
    mov  [r12 + GzipArena.ioCount], eax
    mov  esi, [r12 + GzipArena.inputLength]
    add  [r12 + GzipArena.inputLength], eax
    add  [r12 + GzipArena.totalInput], eax
    mov  edi, [r12 + GzipArena.ioCount]
    mov  rbx, [r12 + GzipArena.input]
    add  rbx, rsi
crc_byte_head: @placement [remaining := edi]
               @invariant crc32_prefix(transferred - remaining)
               @measure edi
    test edi, edi
    jz   read_head
    movzx edx, byte ptr [rbx]
    mov  eax, [r12 + GzipArena.crc]
    xor  al, dl
    mov  ecx, 8
crc_bit_head: @measure ecx
    mov  edx, eax
    and  edx, 1
    neg  edx
    shr  eax, 1
    and  edx, 0xedb88320
    xor  eax, edx
    dec  ecx
    jnz  crc_bit_head
    mov  [r12 + GzipArena.crc], eax
    inc  rbx
    dec  edi
    jmp  crc_byte_head

process_nonfinal_block:
    xor  ecx, ecx                        ; BFINAL = 0
    call_local process_block
    test eax, eax
    jnz  route_io_error
    mov  dword ptr [r12 + GzipArena.inputLength], 0
    jmp  read_head

input_eof:
    mov  ecx, 1                          ; BFINAL = 1, partial or empty
    call_local process_block
    test eax, eax
    jnz  route_io_error
    call_local align_writer
    test eax, eax
    jnz  route_io_error
    mov  eax, [r12 + GzipArena.crc]
    not  eax
    mov  ebx, eax
    mov  esi, 4
trailer_crc_head: @measure esi
    movzx eax, bl
    call_local emit_raw_byte
    test eax, eax
    jnz  route_io_error
    shr  ebx, 8
    dec  esi
    jnz  trailer_crc_head
    mov  ebx, [r12 + GzipArena.totalInput]
    mov  esi, 4
trailer_size_head: @measure esi
    movzx eax, bl
    call_local emit_raw_byte
    test eax, eax
    jnz  route_io_error
    shr  ebx, 8
    dec  esi
    jnz  trailer_size_head
    call_local flush_output
    test eax, eax
    jnz  route_io_error
    jmp  exit_success

; process_block(ecx=final) emits header, tokens, and EOB.
process_block: @contract fixed_block_refines_input
    push rbx
    push rbp
    push rsi
    push rdi
    push r13
    push r14
    push r15
    sub  rsp, ProcessBlockFrame.size
    mov  ebp, ecx
    mov  rdi, [r12 + GzipArena.head]
    mov  ecx, 65536
    mov  ax, 0xffff
    cld
    rep  stosw                            ; initialize every current-generation head
    mov  dword ptr [r12 + GzipArena.position], 0
    mov  eax, ebp
    or   eax, 2                           ; BTYPE bits 01 after BFINAL
    mov  ecx, 3
    call_local emit_bits
    test eax, eax
    jnz  process_block_return
token_head: @invariant token_prefix_expands_to_input_prefix(position)
            @measure inputLen-position
    mov  esi, [r12 + GzipArena.position]
    cmp  esi, [r12 + GzipArena.inputLength]
    jae  token_eob
    mov  eax, [r12 + GzipArena.inputLength]
    sub  eax, esi
    cmp  eax, 3
    jb   token_literal
    mov  rdi, [r12 + GzipArena.input]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rbx, [r12 + GzipArena.head]
    movzx r13d, word ptr [rbx+rax*2]     ; old head/candidate
    mov  rdx, [r12 + GzipArena.prev]
    mov  word ptr [rdx+rsi*2], r13w
    mov  word ptr [rbx+rax*2], si        ; insert current position
    mov  r14d, 2                         ; best length
    xor  r15d, r15d                      ; best distance
    mov  ebx, 64                         ; reviewed finite search budget
candidate_head: @invariant candidates_strictly_precede_position
                @measure (ebx, chain_rank)
    test ebx, ebx
    jz   candidate_done
    cmp  r13d, 0xffff
    je   candidate_done
    cmp  r13d, esi
    jae  dictionary_violation
    mov  eax, esi
    sub  eax, r13d                       ; distance
    cmp  eax, 32768
    ja   candidate_next                  ; defensive under block bound
    mov  ebp, [r12 + GzipArena.inputLength]
    sub  ebp, esi
    cmp  ebp, 258
    jbe  compare_setup
    mov  ebp, 258
compare_setup:
    xor  ecx, ecx                        ; candidate length
    mov  rdi, [r12 + GzipArena.input]
compare_head: @measure ebp-ecx
    cmp  ecx, ebp
    jae  compare_done
    mov  r8d, r13d
    add  r8d, ecx
    movzx r9d, byte ptr [rdi+r8]
    mov  r10d, esi
    add  r10d, ecx
    cmp  r9b, byte ptr [rdi+r10]
    jne  compare_done
    inc  ecx
    jmp  compare_head
compare_done:
    cmp  ecx, r14d
    jbe  candidate_next                  ; equal keeps nearer visited match
    mov  r14d, ecx
    mov  r15d, esi
    sub  r15d, r13d
    cmp  ecx, ebp
    je   candidate_done
candidate_next:
    mov  rdx, [r12 + GzipArena.prev]
    movzx r13d, word ptr [rdx+r13*2]
    dec  ebx
    jmp  candidate_head
candidate_done:
    cmp  r14d, 3
    jb   token_literal_after_insert
    mov  ecx, r14d
    mov  edx, r15d
    call_local emit_reference
    test eax, eax
    jnz  process_block_return
    mov  ebx, esi
    add  ebx, r14d                       ; exclusive consumed end
    inc  esi                             ; position zero already inserted
insert_consumed_head: @placement [cursor := esi]
                      @invariant inserted_range(oldPosition, cursor)
                      @measure ebx-esi
    cmp  esi, ebx
    jae  reference_advance
    mov  eax, [r12 + GzipArena.inputLength]
    sub  eax, esi
    cmp  eax, 3
    jb   insert_consumed_skip
    mov  rdi, [r12 + GzipArena.input]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rdi, [r12 + GzipArena.head]
    movzx ecx, word ptr [rdi+rax*2]
    mov  rdx, [r12 + GzipArena.prev]
    mov  word ptr [rdx+rsi*2], cx
    mov  word ptr [rdi+rax*2], si
insert_consumed_skip:
    inc  esi
    jmp  insert_consumed_head
reference_advance:
    mov  [r12 + GzipArena.position], ebx
    jmp  token_head
token_literal_after_insert:
token_literal:
    mov  rdi, [r12 + GzipArena.input]
    movzx ecx, byte ptr [rdi+rsi]
    call_local emit_fixed_symbol
    test eax, eax
    jnz  process_block_return
    inc  esi
    mov  [r12 + GzipArena.position], esi
    jmp  token_head
token_eob:
    mov  ecx, 256
    call_local emit_fixed_symbol
process_block_return:
    add  rsp, ProcessBlockFrame.size
    pop  r15
    pop  r14
    pop  r13
    pop  rdi
    pop  rsi
    pop  rbp
    pop  rbx
    ret
dictionary_violation:
    mov  eax, 4                          ; model violation, never normal data
    jmp  process_block_return

; emit_reference(ecx=length, edx=distance), both already certified.
emit_reference:
    push rbx
    push rsi
    push rdi
    sub  rsp, EmitReferenceFrame.size
    mov  ebx, ecx
    mov  esi, edx
    xor  edi, edi
length_code_head: @measure 29-edi
    cmp  edi, 28
    je   length_code_found
    lea  r9, [rip + lengthBase]
    movzx eax, word ptr [r9+rdi*2]
    movzx edx, word ptr [r9+rdi*2+2]
    cmp  ebx, eax
    jb   reference_impossible
    cmp  ebx, edx
    jb   length_code_found
    inc  edi
    jmp  length_code_head
length_code_found:
    lea  ecx, [rdi+257]
    call_local emit_fixed_symbol
    test eax, eax
    jnz  reference_return
    lea  r9, [rip + lengthExtra]
    movzx ecx, byte ptr [r9+rdi]
    test ecx, ecx
    jz   distance_lookup
    lea  r9, [rip + lengthBase]
    movzx eax, word ptr [r9+rdi*2]
    mov  edx, ebx
    sub  edx, eax
    mov  eax, edx
    call_local emit_bits
    test eax, eax
    jnz  reference_return
distance_lookup:
    xor  edi, edi
distance_code_head: @measure 30-edi
    cmp  edi, 29
    je   distance_code_found
    lea  r9, [rip + distanceBase]
    movzx eax, word ptr [r9+rdi*2]
    movzx edx, word ptr [r9+rdi*2+2]
    cmp  esi, eax
    jb   reference_impossible
    cmp  esi, edx
    jb   distance_code_found
    inc  edi
    jmp  distance_code_head
distance_code_found:
    mov  eax, edi
    mov  ecx, 5
    call_local reverse_low_bits
    mov  ecx, 5
    call_local emit_bits
    test eax, eax
    jnz  reference_return
    lea  r9, [rip + distanceExtra]
    movzx ecx, byte ptr [r9+rdi]
    test ecx, ecx
    jz   reference_ok
    lea  r9, [rip + distanceBase]
    movzx eax, word ptr [r9+rdi*2]
    mov  edx, esi
    sub  edx, eax
    mov  eax, edx
    call_local emit_bits
    jmp  reference_return
reference_ok:
    xor  eax, eax
reference_return:
    add  rsp, EmitReferenceFrame.size
    pop  rdi
    pop  rsi
    pop  rbx
    ret
reference_impossible:
    mov  eax, 4
    jmp  reference_return

; emit_fixed_symbol(ecx=0..287): derive canonical fixed code, reverse it,
; then feed the LSB-first bit writer.
emit_fixed_symbol:
    sub  rsp, EmitFixedSymbolFrame.size
    cmp  ecx, 143
    ja   fixed_144
    lea  eax, [rcx+0x30]
    mov  ecx, 8
    jmp  fixed_reverse
fixed_144:
    cmp  ecx, 255
    ja   fixed_256
    lea  eax, [rcx+0x100]                ; 0x190 + (sym-144)
    mov  ecx, 9
    jmp  fixed_reverse
fixed_256:
    cmp  ecx, 279
    ja   fixed_280
    lea  eax, [rcx-256]
    mov  ecx, 7
    jmp  fixed_reverse
fixed_280:
    cmp  ecx, 287
    ja   fixed_symbol_impossible
    lea  eax, [rcx-88]                   ; 0xc0 + (sym-280)
    mov  ecx, 8
fixed_reverse:
    mov  r10d, ecx                       ; retain bit count
    call_local reverse_low_bits          ; eax=value, ecx=count -> eax
    mov  ecx, r10d
    call_local emit_bits
    add  rsp, EmitFixedSymbolFrame.size
    ret
fixed_symbol_impossible:
    mov  eax, 4
    add  rsp, EmitFixedSymbolFrame.size
    ret

; reverse_low_bits(eax=value, ecx=count) -> eax.
reverse_low_bits:
    xor  edx, edx
reverse_head: @measure ecx
    test ecx, ecx
    jz   reverse_done
    shl  edx, 1
    mov  r8d, eax
    and  r8d, 1
    or   edx, r8d
    shr  eax, 1
    dec  ecx
    jmp  reverse_head
reverse_done:
    mov  eax, edx
    ret

; emit_bits(eax=value, ecx=count<=16). The contract proves high bits ignored.
emit_bits:
    push rbx
    sub  rsp, EmitBitsFrame.size
    mov  r10d, ecx
    mov  edx, 1
    mov  ecx, r10d
    shl  edx, cl
    dec  edx
    and  eax, edx
    mov  edx, [r12 + GzipArena.bitCount]
    mov  r8, [r12 + GzipArena.bitAccumulator]
    mov  r9, rax
    mov  cl, dl
    shl  r9, cl
    or   r8, r9
    add  edx, r10d
emit_full_byte_head: @invariant bitAccRep(bitAcc,bitCount)
                     @measure edx
    cmp  edx, 8
    jb   emit_bits_store
    cmp  dword ptr [r12 + GzipArena.outputLength], GzipArena.outputBytes.size
    jne  emit_bits_space
    mov  [r12 + GzipArena.bitAccumulator], r8
    mov  [r12 + GzipArena.bitCount], edx
    call_local flush_output
    test eax, eax
    jnz  emit_bits_return
    mov  r8, [r12 + GzipArena.bitAccumulator]
    mov  edx, [r12 + GzipArena.bitCount]
emit_bits_space:
    mov  rbx, [r12 + GzipArena.output]
    mov  ecx, [r12 + GzipArena.outputLength]
    mov  byte ptr [rbx+rcx], r8b
    inc  ecx
    mov  [r12 + GzipArena.outputLength], ecx
    shr  r8, 8
    sub  edx, 8
    jmp  emit_full_byte_head
emit_bits_store:
    mov  [r12 + GzipArena.bitAccumulator], r8
    mov  [r12 + GzipArena.bitCount], edx
    xor  eax, eax
emit_bits_return:
    add  rsp, EmitBitsFrame.size
    pop  rbx
    ret

; align_writer appends zero padding until the next byte boundary.
align_writer:
    mov  ecx, [r12 + GzipArena.bitCount]
    test ecx, ecx
    jz   align_done
    mov  edx, 8
    sub  edx, ecx
    xor  eax, eax
    mov  ecx, edx
    jmp  emit_bits
align_done:
    xor  eax, eax
    ret

; emit_raw_byte(eax=byte), valid only with bitCount=0.
emit_raw_byte:
    push rbx
    sub  rsp, EmitRawByteFrame.size
    mov  ebx, eax
    cmp  dword ptr [r12 + GzipArena.bitCount], 0
    jne  raw_byte_impossible
    cmp  dword ptr [r12 + GzipArena.outputLength], GzipArena.outputBytes.size
    jne  raw_byte_space
    call_local flush_output
    test eax, eax
    jnz  raw_byte_return
raw_byte_space:
    mov  rdx, [r12 + GzipArena.output]
    mov  ecx, [r12 + GzipArena.outputLength]
    mov  byte ptr [rdx+rcx], bl
    inc  ecx
    mov  [r12 + GzipArena.outputLength], ecx
    xor  eax, eax
raw_byte_return:
    add  rsp, EmitRawByteFrame.size
    pop  rbx
    ret
raw_byte_impossible:
    mov  eax, 4
    jmp  raw_byte_return

; flush_output: complete partial-write loop over output[0..outLen).
flush_output:
    push rbx
    push rsi
    push rdi
    sub  rsp, FlushFrame.size
    xor  ebx, ebx                        ; consumed
flush_head: @invariant SliceConsumerInvariant(output,consumed,outLen)
            @frontier_or_measure(write_or_remaining)
    mov  esi, [r12 + GzipArena.outputLength]
    cmp  ebx, esi
    jae  flush_done
    mov  edi, esi
    sub  edi, ebx
    mov  [r12 + GzipArena.ioRequest], edi
    mov  rcx, [r12 + GzipArena.stdout]
    mov  rdx, [r12 + GzipArena.output]
    add  rdx, rbx
    mov  r8d, [r12 + GzipArena.ioRequest]
    lea  r9, [rsp + FlushFrame.transferred]
    mov  dword ptr [rsp + FlushFrame.transferred], 0
    mov  qword ptr [rsp + FlushFrame.overlapped], 0
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   flush_failed
    mov  eax, [rsp + FlushFrame.transferred]
    cmp  eax, [r12 + GzipArena.ioRequest]
    ja   flush_violation
    test eax, eax
    jz   flush_no_progress
    add  ebx, eax
    jmp  flush_head
flush_done:
    mov  dword ptr [r12 + GzipArena.outputLength], 0
    xor  eax, eax
    jmp  flush_return
flush_failed:
    mov  eax, 1
    jmp  flush_return
flush_no_progress:
    mov  eax, 2
    jmp  flush_return
flush_violation:
    mov  eax, 3
flush_return:
    add  rsp, FlushFrame.size
    pop  rdi
    pop  rsi
    pop  rbx
    ret

route_io_error:
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    cmp  eax, 3
    je   write_count_violation @violation_edge(.excessWriteCount)
    jmp  dictionary_violation_terminal @violation_edge(.internalCodecInvariant)

stdin_unavailable:      @terminal(.stdinUnavailable)
    mov  ecx, 1
    jmp  exit
stdout_unavailable:     @terminal(.stdoutUnavailable)
    mov  ecx, 1
    jmp  exit
resource_exhausted_no_root: @terminal(.resourceExhausted)
    mov  ecx, 1
    jmp  exit
read_failed:            @terminal(.readFailed)
    mov  ecx, 1
    jmp  exit
write_failed:           @terminal(.writeFailed)
    mov  ecx, 1
    jmp  exit
no_progress:            @terminal(.noProgress)
    mov  ecx, 1
    jmp  exit
exit_success:           @terminal(.success)
    xor  ecx, ecx
exit:
    call qword ptr [rip + __imp_ExitProcess]
    ud2 @containment_tail(.terminalUnexpectedReturn)
read_count_violation:
    ud2 @containment_tail(.excessReadCount)
write_count_violation:
    ud2 @containment_tail(.excessWriteCount)
dictionary_violation_terminal:
    ud2 @containment_tail(.internalCodecInvariant)
}
```

The internal helper ABI is deliberately small and checkable. Calls enter with
`rsp mod 16 = 8`; every helper that calls again adjusts to `rsp mod 16 = 0`
before its `call`. `process_block` saves seven registers and reserves 48 bytes;
`emit_reference` and `flush_output` save three and reserve 32/48 bytes;
`emit_fixed_symbol` reserves 40; `emit_bits` and `emit_raw_byte` save one and
reserve 32. Leaf `reverse_low_bits` uses no frame. `align_writer` performs a
true tail jump only when it delegates to `emit_bits`. All helpers preserve
`rbx`, `rbp`, `rsi`, `rdi`, and `r12`–`r15`; the fixed-symbol path keeps its bit
count in `r10d` across `reverse_low_bits`, whose explicit clobber set excludes
`r10`. The bit writer similarly copies its incoming count to `r10d` before
using `cl` for shifts. No value is recovered from an imaginary stack slot.

Return code four is reserved for a proved-unreachable internal codec invariant
failure (bad symbol/range, unaligned raw byte, or nondecreasing dictionary
link). It is never conflated with an excess `WriteFile` count. Normal
verification proves no conforming execution reaches it; retaining the physical
edge makes a failed model assertion loud in the raw artifact.

## 7. Static tables, raw bytes, and relocations

These are the complete non-code codec tables. The PE writer serializes each
typed array exactly as shown and proves its parser round trip; it does not rely
on assembler-private data.

```lean
def lengthBase : Vec UInt16 29 :=
  #[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,
    131,163,195,227,258]
def lengthExtra : Vec UInt8 29 :=
  #[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0]
def distanceBase : Vec UInt16 30 :=
  #[1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,
    1537,2049,3073,4097,6145,8193,12289,16385,24577]
def distanceExtra : Vec UInt8 30 :=
  #[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]
```

`.rdata` contains only these four arrays. `.text` contains exactly the erased
instructions above. The IAT contains exactly six imports from `kernel32.dll`:
`GetStdHandle`, `GetProcessHeap`, `HeapAlloc`, `ReadFile`, `WriteFile`, and
`ExitProcess`. Every IAT reference is RIP-relative. Direct helper/CFG edges use
signed rel32 relocations resolved by the linker. No absolute image address,
runtime library, writable global, TLS callback, export, or hidden startup stub is
present.

The matching `Assembly.lean` owns these four typed arrays, their exact
static-object table, and the first-class machine source. The elaborator derives
the six-entry import declaration, closes the source as `gzipSourceClosure`,
derives `gzipExpandedSource`, and proves
`gzipExpansionExact`. The expanded source, component binding, and expansion
identity are explicit inputs to `verify_assembly`, so table bytes are verified
source rather than prose surrounding it. `gzipSourceClosureComplete` rejects
unresolved references and `gzipExpandedListingExact` identifies the reviewed
listing with the generated raw source.

Each mnemonic/operand tuple elaborates to an exact raw instruction constructor,
not an unconstrained assembler request. The reviewed x86 encoder policy chooses
the canonical shortest applicable immediate/displacement form and performs
monotone branch relaxation to a proved fixed point; an author may instead pin a
longer exact encoding. The artifact records that choice, so decoding `.text`
recovers semantically identical raw instructions even where x86 has aliases.
Changing the encoding policy regenerates layout/relocations/bytes and their
proofs without reopening codec semantics.

## 8. Local proof burden

The proof annotations generate these independent obligations:

- every instruction is applicable under common Intel/AMD x86-64 and its cited
  fault/interrupt/memory semantics;
- entry/call/return stack shape, 32-byte Win64 shadow space, nonvolatile saves,
  result slots, and unwind state agree at every edge;
- all shifts, scaled addresses, table reads, block offsets, and buffer writes are
  in range; no proof relies on a successful concrete run;
- dictionary links are initialized, generation-local, strictly decreasing, and
  therefore cycle-free; the 64-probe measure is real even without that theorem;
- each accepted match certifies byte equality for its complete length, including
  the decoder's overlapping-copy interpretation;
- token expansion preserves the exact input prefix; choosing a literal or any
  certified match preserves it without proving `findMatch` optimal;
- fixed-symbol and length/distance formulas match RFC 1951 for every possible
  operand, with `bv_decide` permitted only for complete finite bit-vector cases;
- bit accumulation, output initialization, CRC, modular ISIZE, and finality
  invariants hold universally across block and API fragmentation boundaries;
- read/write dependent returns initialize/consume exactly their reported slices,
  return exact loan identities, and separate normal failure from violation;
- finite internal loops decrease; API waits are explicit frontiers; infinite
  input remains productive and bounded-memory;
- terminal status and root-obligation disposition match every outcome; and
- the audit-violation ledger remains empty on every conforming execution.

Standard automation should close instruction composition, arithmetic side
conditions, ABI frames, slice loans, CRC step algebra, table lookup, bit-writer
steps, and PE structure. The author should see the algorithmic invariants,
reference-validity argument, block finality, progress frontiers, and genuinely
nonstandard containment choices. If the author must restate byte-array algebra
for every instruction, the library boundary has failed.

## 9. Erasure and exact Win64 PE

```lean
theorem gzip_erasure :
  ErasurePreservesSemantics
    gzipVerified.ghostProgram gzipVerified.rawProgram :=
  gzipVerified.erasureCorrectness

theorem emission_exact :
  emitProgram gzipVerified = PE.write gzipVerified.linkedArtifact

theorem pe_round_trip :
  PE.parse (emitProgram gzipVerified) = .ok gzipVerified.linkedArtifact

theorem gzip_artifact_connection :
  ArtifactRepresents gzipVerified.rawProgram gzipVerified.linkedArtifact :=
  gzipVerified.artifactCorrectness

theorem gzip_emitted_sound := gzipVerified.sound
```

The linked PE32+ has `.text` `R-X`, `.rdata` `R--`, `.idata` with loader-time IAT
write authority and final standard permissions, and generated `.pdata/.xdata`
for every non-leaf frame. It sets `DYNAMIC_BASE` and `NX_COMPAT`; all internal
data references are RVA/RIP-relative. Imports are derived from the exact raw
program. The abstract loader parses these exact bytes, chooses each admissible
ASLR base, maps sections, resolves the six exact ABI profiles, removes temporary
write authority, reconstructs the decoded raw CFG, and transfers control to
`entry`.

`gzipVerified.sound` quantifies over every admissible execution context, exact-
artifact load base, and exact-artifact import environment. Loaded execution is
coupled to raw execution under the same namespaced provider choices, then to the
ghost construction and portable observation. Success yields one member decoding
to the input. Failure yields the stated silent or construction-prefix result.
Infinite executions carry safety and progress facts without a fabricated exit.

## 10. Proof locality and SDLC

| Change | Precious edit | Process-plan edit | Platform/assembly edit | Expected invalidation |
| --- | --- | --- | --- | --- |
| chain probes 64 -> 128 | none | none | codec policy and `candidate_head` immediate | search progress/performance and local artifact; process/spec proofs reused |
| one encoder -> CRC/LZ/bit-writer pipeline | none | kinds, channels, ownership, composition | corresponding source boundaries | weave/progress and local realization; root and codec relation reused |
| fixed -> dynamic Huffman | none | encoder realization only if its protocol is unchanged | tables and assembly sub-CFG | encoder realization/artifact; root and console proofs reused |
| 32 KiB block size | none | none unless channel buffering changes | layout and block/dictionary policy | memory/search/block certificates; process/spec proofs reused |
| require deterministic bytes publicly | strengthen spec and perhaps encoder protocol | reprove outer realization | possibly none | all implementations and outer `VerifiedProgram spec` theorem |
| permit multiple members | change observation/protocol | root/encoder composition | codec plan optional | spec/process refinement; memory and Win32 I/O may remain |
| add `-d` CLI | extend spec and abstract process demands | add inflate process and routing | argv provider and inflate CFG | new protocol/weave/provider cones; compressor child remains reusable |
| ReadFile becomes adaptive overlapped I/O | none | supervision only if observable scheduling changes | platform plan and I/O blocks | driver/liveness/ABI/artifact; codec/root functional proofs reused |
| CRC implementation becomes table/PCLMUL | none | none | CRC sub-CFG/profile | local ISA/refinement/artifact; encoder protocol reused |
| PE layout changes | none | none | linker policy if reviewed | artifact/parser/loader only |

The dependency report must name causal paths and distinguish re-elaboration,
re-proof, and regeneration. A clean rebuild is only a reproducibility check.
Unexplained whole-program proof churn from a CRC or PE-layout change rejects the
library boundary.

## 11. Validation and adversarial review

Proof is paired with, not replaced by:

- RFC and boundary vectors: empty, one byte, 32,767/32,768/32,769 bytes,
  repeated bytes, maximum length/distance, incompressible bytes, and ISIZE wrap;
- differential decompression by at least two independent mature implementations;
- differential parsing of stored/fixed/dynamic members, optional headers,
  concatenated members, corrupt trees, bad distances, CRC/ISIZE mismatch, and
  every truncation point;
- randomized read/write fragmentation, zero progress, failure, excess count,
  and nonresponsive strategies;
- model-versus-hardware probes for every selected instruction on Intel and AMD;
- exact PE parse/load/import/unwind/ASLR probes; and
- performance and compression-ratio budgets labeled as product regressions, not
  theorem substitutes.

Review must answer two separate questions. Is the portable specification the
smallest honest meaning of a gzip filter? Is this fixed-block bounded-search
artifact something worth shipping for its stated profile? A “yes” to the proof
does not silently answer the product question.

## 12. Sources and verification instructions

Normative format anchors:

- RFC 1952, GZIP file format: https://www.rfc-editor.org/rfc/rfc1952
- RFC 1951, DEFLATE compressed data format: https://www.rfc-editor.org/rfc/rfc1951
- RFC 1950, zlib wrapper format (standard-library companion):
  https://www.rfc-editor.org/rfc/rfc1950

Platform anchors:

- Microsoft `ReadFile`:
  https://learn.microsoft.com/windows/win32/api/fileapi/nf-fileapi-readfile
- Microsoft `WriteFile`:
  https://learn.microsoft.com/windows/win32/api/fileapi/nf-fileapi-writefile
- Microsoft process heap and `HeapAlloc`:
  https://learn.microsoft.com/windows/win32/api/heapapi/nf-heapapi-getprocessheap
  and https://learn.microsoft.com/windows/win32/api/heapapi/nf-heapapi-heapalloc
- Microsoft `GetStdHandle` and `ExitProcess`:
  https://learn.microsoft.com/windows/console/getstdhandle and
  https://learn.microsoft.com/windows/win32/api/processthreadsapi/nf-processthreadsapi-exitprocess
- Microsoft x64 ABI/unwind and PE/COFF:
  https://learn.microsoft.com/cpp/build/x64-calling-convention and
  https://learn.microsoft.com/windows/win32/debug/pe-format

All web anchors in this draft were retrieved 2026-09-01. Acceptance records the
document revision/date and stable section anchor in the corpus source ledger;
an unversioned URL alone is insufficient implementation authority.

For every format clause, reviewers open the cited RFC section and compare the
bit/byte order, ranges, reserved cases, and error behavior to the transparent
Lean definition and the displayed table. For every API occurrence, reviewers
open the current Microsoft page, record retrieval date/profile assumptions, and
compare all parameters, pending/failure returns, output initialization, partial
completion, and handle-mode requirements. Vendor ISA citations and probes follow
[INSTRUCTIONS.md](INSTRUCTIONS.md); corpus-level retrieval metadata belongs in
[REFERENCES.md](REFERENCES.md) when this design is accepted.

The selected instruction inventory is closed for this artifact: MOV/LEA,
PUSH/POP, ADD/SUB/INC/DEC/NEG, IMUL, AND/OR/XOR/NOT, SHL/SHR, CMP/TEST, direct
and indirect CALL, RET, conditional/unconditional branches, CLD/REP STOSW, and
UD2. Each exact operand/encoding form receives both an Intel SDM Volume 2 anchor
and the corresponding AMD64 APM Volume 3 anchor in the instruction registry;
the common profile chooses only their proved intersection. Changing a helper to
use CRC32, PCLMULQDQ, AVX, BMI, or another extension changes this inventory and
requires a feature-specific realization plus its own citations and probes.

## 13. Open review questions

1. Is successful decompression-to-input the right precious observation, or must
   the first spec also demand deterministic bytes for reproducible builds?
2. Is a one-member compressor-only filter sufficiently “gzip,” provided the
   full reader and zlib/DEFLATE pieces are standard-library work, or should a
   decompression entry be in this same spike?
3. Is fixed Huffman plus bounded greedy search a shippable first artifact, or is
   dynamic-Huffman emission a product requirement even though it adds no new
   semantic guarantee?
4. Should read failure after emission permit a construction prefix, or should a
   spool/transactional provider be required for empty output on every input
   failure at the cost of bounded-memory streaming?
5. Should the initial Windows provider remain explicitly synchronous, or must
   this artifact handle inherited overlapped standard handles adaptively?
6. Does one arena/root obligation make the ownership proof appropriately small,
   or does it hide useful independent lifetime pressure the spike should expose?
7. Should block dictionaries reset, as proposed, or should the standard codec
   boundary require a 32 KiB history carried across blocks?


## Exact authored source snapshot

This section is the author-maintained Lean surface defined by
[SPIKE_AUTHORING.md](SPIKE_AUTHORING.md). Earlier code blocks in this document
are generated expansions, library interface sketches, or proof sketches unless
they are explicitly labeled authored source. Reviewers must compare this
snapshot with `Spikes/3_Gzip/` exactly.

### `Assembly.lean`

```lean
import Grass.Assembly.X86
import Grass.Platform.Win10.X64
import Grass.Process.Sequential
import Grass.Std.Zlib.Fixed32K
import Spikes.«3_Gzip».Spec

namespace Grass.Spikes.Gzip

def policy : TargetOutcomeProjection GzipOutcome UInt32 :=
  .successOrFailure
    (success := GzipOutcome.success)
    (successCode := 0)
    (failureCode := 1)

def projection : TargetProjection spec .win10X64 :=
  TargetProjection.win10ByteStreams policy

def processRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)

def codecPlan : GzipImplementationPlan :=
  .fixed32KHashChain (maxProbes := 64)

def fixed32KContract : ComponentContract :=
  Std.Zlib.Fixed32K.contract codecPlan

def fixed32KModel : ImplementationModel :=
  Std.Zlib.Fixed32K.model codecPlan

theorem fixed32KModelCorrect :
    ImplementationRealizesContract fixed32KModel fixed32KContract :=
  Std.Zlib.Fixed32K.correct codecPlan

theorem fixed32KRoundTrip (input : ByteArray) :
    Std.Zlib.inflate (Std.Zlib.Fixed32K.write codecPlan input) = .ok input :=
  Std.Zlib.Fixed32K.roundTrip codecPlan input

def platformPlan : PlatformPlan spec.driverBoundary.requirements :=
  PlatformPlan.win10X64StreamingIO projection

def lengthBase : Vec UInt16 29 :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43,
    51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]

def lengthExtra : Vec UInt8 29 :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3,
    4, 4, 4, 4, 5, 5, 5, 5, 0]

def distanceBase : Vec UInt16 30 :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257,
    385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385,
    24577]

def distanceExtra : Vec UInt8 30 :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8,
    9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

def gzipStaticObjects : StaticObjectTable := static_objects {
  rodata align 2 {
    lengthBase: uint16s lengthBase
    lengthExtra: uint8s lengthExtra
    distanceBase: uint16s distanceBase
    distanceExtra: uint8s distanceExtra
  }
}

structure GzipMachineState where
  input : OwnedBuffer
  window : OwnedBuffer
  head : OwnedBuffer
  prev : OwnedBuffer
  tokens : OwnedBuffer
  output : OwnedBuffer
  crc : UInt32
  inputSize : UInt32
  bitAccumulator : UInt64
  bitCount : UInt8
  blockLength : UInt32
  generation : UInt16
  phase : GzipPhase

structure GzipFrameFields where
  shadow : Bytes 32
  overlapped : UInt64
  transferred : UInt32
  locals : Bytes 28

def GzipFrame : FrameLayout Win64 := FrameLayout.derive GzipFrameFields

structure GzipArenaFields where
  heap : UInt64
  stdin : UInt64
  stdout : UInt64
  inputLength : UInt32
  position : UInt32
  outputLength : UInt32
  bitCount : UInt32
  bitAccumulator : UInt64
  crc : UInt32
  totalInput : UInt32
  root : UInt64
  input : UInt64
  head : UInt64
  prev : UInt64
  output : UInt64
  ioRequest : UInt32
  ioCount : UInt32
  reserved : Bytes 152
  inputBytes : Bytes 32768
  headEntries : Bytes 131072
  prevEntries : Bytes 65536
  outputBytes : Bytes 65536

def GzipArena : StructLayout Win64 := StructLayout.derive GzipArenaFields

structure GzipHeaderFields where
  magic : UInt16
  compressionMethod : UInt8
  flags : UInt8
  modificationTime : UInt32
  extraFlags : UInt8
  operatingSystem : UInt8

def GzipHeader : PackedStructLayout :=
  PackedStructLayout.derive GzipHeaderFields

def ProcessBlockFrame :=
  Win64.callFrameAfterSaves #[rbx, rbp, rsi, rdi, r13, r14, r15]

def EmitReferenceFrame := Win64.callFrameAfterSaves #[rbx, rsi, rdi]

def EmitFixedSymbolFrame := Win64.callFrameAfterSaves #[]

def EmitBitsFrame := Win64.callFrameAfterSaves #[rbx]

def EmitRawByteFrame := Win64.callFrameAfterSaves #[rbx]

structure FlushFrameFields where
  shadow : Bytes 32
  overlapped : UInt64
  transferred : UInt32

def FlushFrame : FrameLayout Win64 := FrameLayout.derive FlushFrameFields

def gzipSource : AsmSource platformPlan := asm_source using codecPlan {

entry:
    push rbx
    push rbp
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    sub  rsp, GzipFrame.size
    mov  ecx, STD_INPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdin_unavailable
    cmp  rax, -1
    je   stdin_unavailable
    mov  r13, rax
    mov  ecx, STD_OUTPUT_HANDLE
    call qword ptr [rip + __imp_GetStdHandle]
    test rax, rax
    jz   stdout_unavailable
    cmp  rax, -1
    je   stdout_unavailable
    mov  r14, rax
    call qword ptr [rip + __imp_GetProcessHeap]
    test rax, rax
    jz   resource_exhausted_no_root
    mov  rbx, rax
    mov  rcx, rbx
    xor  edx, edx
    mov  r8d, GzipArena.size
    call qword ptr [rip + __imp_HeapAlloc]
    test rax, rax
    jz   resource_exhausted_no_root
    mov  r12, rax
    mov  [r12 + GzipArena.heap], rbx
    mov  [r12 + GzipArena.stdin], r13
    mov  [r12 + GzipArena.stdout], r14
    mov  [r12 + GzipArena.root], r12
    lea  rax, [r12 + GzipArena.inputBytes]
    mov  [r12 + GzipArena.input], rax
    lea  rax, [r12 + GzipArena.headEntries]
    mov  [r12 + GzipArena.head], rax
    lea  rax, [r12 + GzipArena.prevEntries]
    mov  [r12 + GzipArena.prev], rax
    lea  rax, [r12 + GzipArena.outputBytes]
    mov  [r12 + GzipArena.output], rax
    mov  dword ptr [r12 + GzipArena.inputLength], 0
    mov  dword ptr [r12 + GzipArena.position], 0
    mov  dword ptr [r12 + GzipArena.outputLength], 10
    mov  dword ptr [r12 + GzipArena.bitCount], 0
    mov  qword ptr [r12 + GzipArena.bitAccumulator], 0
    mov  dword ptr [r12 + GzipArena.crc], 0xffffffff
    mov  dword ptr [r12 + GzipArena.totalInput], 0
    mov  rdi, [r12 + GzipArena.output]
    mov  rax, 0x0000000000088b1f
    mov  [rdi + GzipHeader.magic], rax
    mov  word ptr [rdi + GzipHeader.extraFlags], 0xff00
    jmp  read_head

read_head: @invariant collecting_block(state, capacity=32768)
           @frontier_or_measure(read_or_remaining_spare)
    mov  eax, [r12 + GzipArena.inputLength]
    cmp  eax, 32768
    je   process_nonfinal_block
    mov  ecx, 32768
    sub  ecx, eax
    mov  [r12 + GzipArena.ioRequest], ecx
    mov  rcx, [r12 + GzipArena.stdin]
    mov  rdx, [r12 + GzipArena.input]
    add  rdx, rax
    mov  r8d, [r12 + GzipArena.ioRequest]
    lea  r9, [rsp + GzipFrame.transferred]
    mov  dword ptr [rsp + GzipFrame.transferred], 0
    mov  qword ptr [rsp + GzipFrame.overlapped], 0
    call qword ptr [rip + __imp_ReadFile]
    test eax, eax
    jz   read_failed
    mov  eax, [rsp + GzipFrame.transferred]
    cmp  eax, [r12 + GzipArena.ioRequest]
    ja   read_count_violation @violation_edge(.excessReadCount)
    test eax, eax
    jz   input_eof
    mov  [r12 + GzipArena.ioCount], eax
    mov  esi, [r12 + GzipArena.inputLength]
    add  [r12 + GzipArena.inputLength], eax
    add  [r12 + GzipArena.totalInput], eax
    mov  edi, [r12 + GzipArena.ioCount]
    mov  rbx, [r12 + GzipArena.input]
    add  rbx, rsi
crc_byte_head: @placement [remaining := edi]
               @invariant crc32_prefix(transferred - remaining)
               @measure edi
    test edi, edi
    jz   read_head
    movzx edx, byte ptr [rbx]
    mov  eax, [r12 + GzipArena.crc]
    xor  al, dl
    mov  ecx, 8
crc_bit_head: @measure ecx
    mov  edx, eax
    and  edx, 1
    neg  edx
    shr  eax, 1
    and  edx, 0xedb88320
    xor  eax, edx
    dec  ecx
    jnz  crc_bit_head
    mov  [r12 + GzipArena.crc], eax
    inc  rbx
    dec  edi
    jmp  crc_byte_head

process_nonfinal_block:
    xor  ecx, ecx
    call_local process_block
    test eax, eax
    jnz  route_io_error
    mov  dword ptr [r12 + GzipArena.inputLength], 0
    jmp  read_head

input_eof:
    mov  ecx, 1
    call_local process_block
    test eax, eax
    jnz  route_io_error
    call_local align_writer
    test eax, eax
    jnz  route_io_error
    mov  eax, [r12 + GzipArena.crc]
    not  eax
    mov  ebx, eax
    mov  esi, 4
trailer_crc_head: @measure esi
    movzx eax, bl
    call_local emit_raw_byte
    test eax, eax
    jnz  route_io_error
    shr  ebx, 8
    dec  esi
    jnz  trailer_crc_head
    mov  ebx, [r12 + GzipArena.totalInput]
    mov  esi, 4
trailer_size_head: @measure esi
    movzx eax, bl
    call_local emit_raw_byte
    test eax, eax
    jnz  route_io_error
    shr  ebx, 8
    dec  esi
    jnz  trailer_size_head
    call_local flush_output
    test eax, eax
    jnz  route_io_error
    jmp  exit_success


process_block: @implements fixed32KContract using fixed32KModelCorrect
    push rbx
    push rbp
    push rsi
    push rdi
    push r13
    push r14
    push r15
    sub  rsp, ProcessBlockFrame.size
    mov  ebp, ecx
    mov  rdi, [r12 + GzipArena.head]
    mov  ecx, 65536
    mov  ax, 0xffff
    cld
    rep  stosw
    mov  dword ptr [r12 + GzipArena.position], 0
    mov  eax, ebp
    or   eax, 2
    mov  ecx, 3
    call_local emit_bits
    test eax, eax
    jnz  process_block_return
token_head: @invariant token_prefix_expands_to_input_prefix(position)
            @measure inputLen-position
    mov  esi, [r12 + GzipArena.position]
    cmp  esi, [r12 + GzipArena.inputLength]
    jae  token_eob
    mov  eax, [r12 + GzipArena.inputLength]
    sub  eax, esi
    cmp  eax, 3
    jb   token_literal
    mov  rdi, [r12 + GzipArena.input]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rbx, [r12 + GzipArena.head]
    movzx r13d, word ptr [rbx+rax*2]
    mov  rdx, [r12 + GzipArena.prev]
    mov  word ptr [rdx+rsi*2], r13w
    mov  word ptr [rbx+rax*2], si
    mov  r14d, 2
    xor  r15d, r15d
    mov  ebx, 64
candidate_head: @invariant candidates_strictly_precede_position
                @measure (ebx, chain_rank)
    test ebx, ebx
    jz   candidate_done
    cmp  r13d, 0xffff
    je   candidate_done
    cmp  r13d, esi
    jae  dictionary_violation
    mov  eax, esi
    sub  eax, r13d
    cmp  eax, 32768
    ja   candidate_next
    mov  ebp, [r12 + GzipArena.inputLength]
    sub  ebp, esi
    cmp  ebp, 258
    jbe  compare_setup
    mov  ebp, 258
compare_setup:
    xor  ecx, ecx
    mov  rdi, [r12 + GzipArena.input]
compare_head: @measure ebp-ecx
    cmp  ecx, ebp
    jae  compare_done
    mov  r8d, r13d
    add  r8d, ecx
    movzx r9d, byte ptr [rdi+r8]
    mov  r10d, esi
    add  r10d, ecx
    cmp  r9b, byte ptr [rdi+r10]
    jne  compare_done
    inc  ecx
    jmp  compare_head
compare_done:
    cmp  ecx, r14d
    jbe  candidate_next
    mov  r14d, ecx
    mov  r15d, esi
    sub  r15d, r13d
    cmp  ecx, ebp
    je   candidate_done
candidate_next:
    mov  rdx, [r12 + GzipArena.prev]
    movzx r13d, word ptr [rdx+r13*2]
    dec  ebx
    jmp  candidate_head
candidate_done:
    cmp  r14d, 3
    jb   token_literal_after_insert
    mov  ecx, r14d
    mov  edx, r15d
    call_local emit_reference
    test eax, eax
    jnz  process_block_return
    mov  ebx, esi
    add  ebx, r14d
    inc  esi
insert_consumed_head: @placement [cursor := esi]
                      @invariant inserted_range(oldPosition, cursor)
                      @measure ebx-esi
    cmp  esi, ebx
    jae  reference_advance
    mov  eax, [r12 + GzipArena.inputLength]
    sub  eax, esi
    cmp  eax, 3
    jb   insert_consumed_skip
    mov  rdi, [r12 + GzipArena.input]
    add  rdi, rsi
    movzx eax, byte ptr [rdi]
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+1]
    add  eax, edx
    imul eax, eax, 251
    movzx edx, byte ptr [rdi+2]
    add  eax, edx
    and  eax, 0xffff
    mov  rdi, [r12 + GzipArena.head]
    movzx ecx, word ptr [rdi+rax*2]
    mov  rdx, [r12 + GzipArena.prev]
    mov  word ptr [rdx+rsi*2], cx
    mov  word ptr [rdi+rax*2], si
insert_consumed_skip:
    inc  esi
    jmp  insert_consumed_head
reference_advance:
    mov  [r12 + GzipArena.position], ebx
    jmp  token_head
token_literal_after_insert:
token_literal:
    mov  rdi, [r12 + GzipArena.input]
    movzx ecx, byte ptr [rdi+rsi]
    call_local emit_fixed_symbol
    test eax, eax
    jnz  process_block_return
    inc  esi
    mov  [r12 + GzipArena.position], esi
    jmp  token_head
token_eob:
    mov  ecx, 256
    call_local emit_fixed_symbol
process_block_return:
    add  rsp, ProcessBlockFrame.size
    pop  r15
    pop  r14
    pop  r13
    pop  rdi
    pop  rsi
    pop  rbp
    pop  rbx
    ret
dictionary_violation:
    mov  eax, 4
    jmp  process_block_return


emit_reference:
    push rbx
    push rsi
    push rdi
    sub  rsp, EmitReferenceFrame.size
    mov  ebx, ecx
    mov  esi, edx
    xor  edi, edi
length_code_head: @measure 29-edi
    cmp  edi, 28
    je   length_code_found
    lea  r9, [rip + lengthBase]
    movzx eax, word ptr [r9+rdi*2]
    movzx edx, word ptr [r9+rdi*2+2]
    cmp  ebx, eax
    jb   reference_impossible
    cmp  ebx, edx
    jb   length_code_found
    inc  edi
    jmp  length_code_head
length_code_found:
    lea  ecx, [rdi+257]
    call_local emit_fixed_symbol
    test eax, eax
    jnz  reference_return
    lea  r9, [rip + lengthExtra]
    movzx ecx, byte ptr [r9+rdi]
    test ecx, ecx
    jz   distance_lookup
    lea  r9, [rip + lengthBase]
    movzx eax, word ptr [r9+rdi*2]
    mov  edx, ebx
    sub  edx, eax
    mov  eax, edx
    call_local emit_bits
    test eax, eax
    jnz  reference_return
distance_lookup:
    xor  edi, edi
distance_code_head: @measure 30-edi
    cmp  edi, 29
    je   distance_code_found
    lea  r9, [rip + distanceBase]
    movzx eax, word ptr [r9+rdi*2]
    movzx edx, word ptr [r9+rdi*2+2]
    cmp  esi, eax
    jb   reference_impossible
    cmp  esi, edx
    jb   distance_code_found
    inc  edi
    jmp  distance_code_head
distance_code_found:
    mov  eax, edi
    mov  ecx, 5
    call_local reverse_low_bits
    mov  ecx, 5
    call_local emit_bits
    test eax, eax
    jnz  reference_return
    lea  r9, [rip + distanceExtra]
    movzx ecx, byte ptr [r9+rdi]
    test ecx, ecx
    jz   reference_ok
    lea  r9, [rip + distanceBase]
    movzx eax, word ptr [r9+rdi*2]
    mov  edx, esi
    sub  edx, eax
    mov  eax, edx
    call_local emit_bits
    jmp  reference_return
reference_ok:
    xor  eax, eax
reference_return:
    add  rsp, EmitReferenceFrame.size
    pop  rdi
    pop  rsi
    pop  rbx
    ret
reference_impossible:
    mov  eax, 4
    jmp  reference_return



emit_fixed_symbol:
    sub  rsp, EmitFixedSymbolFrame.size
    cmp  ecx, 143
    ja   fixed_144
    lea  eax, [rcx+0x30]
    mov  ecx, 8
    jmp  fixed_reverse
fixed_144:
    cmp  ecx, 255
    ja   fixed_256
    lea  eax, [rcx+0x100]
    mov  ecx, 9
    jmp  fixed_reverse
fixed_256:
    cmp  ecx, 279
    ja   fixed_280
    lea  eax, [rcx-256]
    mov  ecx, 7
    jmp  fixed_reverse
fixed_280:
    cmp  ecx, 287
    ja   fixed_symbol_impossible
    lea  eax, [rcx-88]
    mov  ecx, 8
fixed_reverse:
    mov  r10d, ecx
    call_local reverse_low_bits
    mov  ecx, r10d
    call_local emit_bits
    add  rsp, EmitFixedSymbolFrame.size
    ret
fixed_symbol_impossible:
    mov  eax, 4
    add  rsp, EmitFixedSymbolFrame.size
    ret


reverse_low_bits:
    xor  edx, edx
reverse_head: @measure ecx
    test ecx, ecx
    jz   reverse_done
    shl  edx, 1
    mov  r8d, eax
    and  r8d, 1
    or   edx, r8d
    shr  eax, 1
    dec  ecx
    jmp  reverse_head
reverse_done:
    mov  eax, edx
    ret


emit_bits:
    push rbx
    sub  rsp, EmitBitsFrame.size
    mov  r10d, ecx
    mov  edx, 1
    mov  ecx, r10d
    shl  edx, cl
    dec  edx
    and  eax, edx
    mov  edx, [r12 + GzipArena.bitCount]
    mov  r8, [r12 + GzipArena.bitAccumulator]
    mov  r9, rax
    mov  cl, dl
    shl  r9, cl
    or   r8, r9
    add  edx, r10d
emit_full_byte_head: @invariant bitAccRep(bitAcc,bitCount)
                     @measure edx
    cmp  edx, 8
    jb   emit_bits_store
    cmp  dword ptr [r12 + GzipArena.outputLength], GzipArena.outputBytes.size
    jne  emit_bits_space
    mov  [r12 + GzipArena.bitAccumulator], r8
    mov  [r12 + GzipArena.bitCount], edx
    call_local flush_output
    test eax, eax
    jnz  emit_bits_return
    mov  r8, [r12 + GzipArena.bitAccumulator]
    mov  edx, [r12 + GzipArena.bitCount]
emit_bits_space:
    mov  rbx, [r12 + GzipArena.output]
    mov  ecx, [r12 + GzipArena.outputLength]
    mov  byte ptr [rbx+rcx], r8b
    inc  ecx
    mov  [r12 + GzipArena.outputLength], ecx
    shr  r8, 8
    sub  edx, 8
    jmp  emit_full_byte_head
emit_bits_store:
    mov  [r12 + GzipArena.bitAccumulator], r8
    mov  [r12 + GzipArena.bitCount], edx
    xor  eax, eax
emit_bits_return:
    add  rsp, EmitBitsFrame.size
    pop  rbx
    ret


align_writer:
    mov  ecx, [r12 + GzipArena.bitCount]
    test ecx, ecx
    jz   align_done
    mov  edx, 8
    sub  edx, ecx
    xor  eax, eax
    mov  ecx, edx
    jmp  emit_bits
align_done:
    xor  eax, eax
    ret


emit_raw_byte:
    push rbx
    sub  rsp, EmitRawByteFrame.size
    mov  ebx, eax
    cmp  dword ptr [r12 + GzipArena.bitCount], 0
    jne  raw_byte_impossible
    cmp  dword ptr [r12 + GzipArena.outputLength], GzipArena.outputBytes.size
    jne  raw_byte_space
    call_local flush_output
    test eax, eax
    jnz  raw_byte_return
raw_byte_space:
    mov  rdx, [r12 + GzipArena.output]
    mov  ecx, [r12 + GzipArena.outputLength]
    mov  byte ptr [rdx+rcx], bl
    inc  ecx
    mov  [r12 + GzipArena.outputLength], ecx
    xor  eax, eax
raw_byte_return:
    add  rsp, EmitRawByteFrame.size
    pop  rbx
    ret
raw_byte_impossible:
    mov  eax, 4
    jmp  raw_byte_return


flush_output:
    push rbx
    push rsi
    push rdi
    sub  rsp, FlushFrame.size
    xor  ebx, ebx
flush_head: @invariant SliceConsumerInvariant(output,consumed,outLen)
            @frontier_or_measure(write_or_remaining)
    mov  esi, [r12 + GzipArena.outputLength]
    cmp  ebx, esi
    jae  flush_done
    mov  edi, esi
    sub  edi, ebx
    mov  [r12 + GzipArena.ioRequest], edi
    mov  rcx, [r12 + GzipArena.stdout]
    mov  rdx, [r12 + GzipArena.output]
    add  rdx, rbx
    mov  r8d, [r12 + GzipArena.ioRequest]
    lea  r9, [rsp + FlushFrame.transferred]
    mov  dword ptr [rsp + FlushFrame.transferred], 0
    mov  qword ptr [rsp + FlushFrame.overlapped], 0
    call qword ptr [rip + __imp_WriteFile]
    test eax, eax
    jz   flush_failed
    mov  eax, [rsp + FlushFrame.transferred]
    cmp  eax, [r12 + GzipArena.ioRequest]
    ja   flush_violation
    test eax, eax
    jz   flush_no_progress
    add  ebx, eax
    jmp  flush_head
flush_done:
    mov  dword ptr [r12 + GzipArena.outputLength], 0
    xor  eax, eax
    jmp  flush_return
flush_failed:
    mov  eax, 1
    jmp  flush_return
flush_no_progress:
    mov  eax, 2
    jmp  flush_return
flush_violation:
    mov  eax, 3
flush_return:
    add  rsp, FlushFrame.size
    pop  rdi
    pop  rsi
    pop  rbx
    ret

route_io_error:
    cmp  eax, 1
    je   write_failed
    cmp  eax, 2
    je   no_progress
    cmp  eax, 3
    je   write_count_violation @violation_edge(.excessWriteCount)
    jmp  dictionary_violation_terminal @violation_edge(.internalCodecInvariant)

stdin_unavailable:      @terminal(.stdinUnavailable)
    mov  ecx, 1
    jmp  exit
stdout_unavailable:     @terminal(.stdoutUnavailable)
    mov  ecx, 1
    jmp  exit
resource_exhausted_no_root: @terminal(.resourceExhausted)
    mov  ecx, 1
    jmp  exit
read_failed:            @terminal(.readFailed)
    mov  ecx, 1
    jmp  exit
write_failed:           @terminal(.writeFailed)
    mov  ecx, 1
    jmp  exit
no_progress:            @terminal(.noProgress)
    mov  ecx, 1
    jmp  exit
exit_success:           @terminal(.success)
    xor  ecx, ecx
exit:
    call qword ptr [rip + __imp_ExitProcess]
    ud2 @containment_tail(.terminalUnexpectedReturn)
read_count_violation:
    ud2 @containment_tail(.excessReadCount)
write_count_violation:
    ud2 @containment_tail(.excessWriteCount)
dictionary_violation_terminal:
    ud2 @containment_tail(.internalCodecInvariant)
}

end Grass.Spikes.Gzip
```

### `Program.lean`

```lean
import Grass.Emit
import Grass.Artifact.PE32Plus
import Spikes.«3_Gzip».Assembly

namespace Grass.Spikes.Gzip

def gzipVerified : VerifiedProgram spec := by
  verify_assembly platformPlan
    with gzipSource

def bytes : ByteArray := emitProgram gzipVerified

theorem emittedSound : EmittedProgramSatisfies spec bytes :=
  gzipVerified.sound

def artifact : PE32Plus := gzipVerified.linkedArtifact

theorem writerRoundTrip : PE32Plus.parse (PE32Plus.write artifact) = .ok artifact :=
  artifact.writerRoundTrip

theorem textDecodesExactly :
    LoadedTextDecodesTo artifact gzipVerified.rawProgram :=
  gzipVerified.artifactCorrectness.loadedTextDecodes

theorem emittedExactly : bytes = PE32Plus.write artifact :=
  rfl

end Grass.Spikes.Gzip
```

### `Spec.lean`

```lean
import Grass.Spec.Console
import Grass.Spec.Grammar
import Grass.Spec.Resource

namespace Grass.Spikes.Gzip

def resources : StreamingResourceModel :=
  StreamingResourceModel.console
    |>.withResidentMemory .boundedIndependentOfInputLength

inductive GzipOutcome
  | success
  | allocationFailure
  | inputFailure
  | outputFailure

def gzipMemberFormat : Format Gzip.Member :=
  Gzip.memberFormat

def gzipSuite {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : SpecificationSuite resources :=
  Console.streamingGzipSuite
    (resources := resources)
    (members := .one)
    (outputFormat := gzipMemberFormat)
    (failureOutput := .constructionPrefix)

def gzipSpec {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : SpecProcess resources :=
  SpecProcess.capture (gzipSuite resources)
    |>.withOutcomes GzipOutcome
    |>.withProgress
        (.reactiveBetweenFrontiers
          |>.terminatesUnder [.stdinEventuallyEOF, .environmentResponsive])

theorem gzipSpecCorrect {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) : MeetsAllSpecificationTheorems (gzipSpec resources) :=
  Console.streamingGzipSuiteCaptureCorrect
    resources GzipOutcome gzipMemberFormat

theorem successfulTraceIffOneMemberRoundTrip
    {R : Type} [ResourceModel R] [StreamingFilterResources R]
    (resources : R) (input output : ByteArray) :
    SuccessfulConsoleTrace (gzipSpec resources) input output ↔
      Gzip.IsExactlyOneMember output ∧ Gzip.inflate output = .ok input :=
  Console.streamingGzipContract_success_iff resources GzipOutcome

def spec : SpecProcess resources := gzipSpec resources

end Grass.Spikes.Gzip
```
