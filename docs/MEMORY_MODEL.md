# Memory, provenance, concurrency, and faults

This model is foundational and must be integrated before instruction libraries
grow. It adapts the successful ownership design from gasm while replacing its
late and restrictive integration points.

## 1. State and access chokepoint

All memory-affecting instructions, APIs, macros, loaders, allocators, DMA/device
operations, and external calls declare memory events through one sealed access
interface. Raw mutation of memory bytes, initialization, permissions,
provenance, or race state outside that interface is prohibited.

An access declares at least:

- address expression and byte range;
- read, write, execute, atomic, or device intent;
- required provenance and spatial bounds;
- required initialization and produced initialization;
- required page/section permissions and alignment;
- atomicity and ordering;
- thread/context identity;
- possible architectural faults and partial completion;
- observation and obligation effects.

Authority/audit checks for a proposed access occur before that access substep
commits. Denial preserves the state immediately before the denied substep and
emits a structured audit result. This is distinct from an architectural fault:
multi-access instructions and APIs are represented by ordered substeps or an
explicit commit-prefix model, and their profiles state which earlier completed
effects remain visible when a later substep faults, interrupts, or completes
partially. Grass must not silently assume that a whole instruction is
transactional.

## 2. Regions, allocations, and pointers

Every allocation has a fresh generative identity independent of its numerical
address. Provenance is hierarchical:

```text
provider allocation -> allocator arena/block -> object -> field/subobject
stack reservation -> call frame -> local slot
image mapping -> section -> symbol/object
```

Profiles distinguish sources such as `VirtualAlloc`, process heap, `malloc`,
page-table mapping, kernel heap, bump allocator, stack, mapped file, and device
memory. Address reuse never revives old pointers.

A pointer contains a numerical address and ghost provenance. Stored pointer
representations use shadow provenance associated with the complete pointer
object. Ordinary integer loads do not manufacture provenance.

Pointer-to-integer-to-pointer recovery is permitted only with an additional
proof that the original live provenance still authorizes that value. It is not
automatic. A typed whole-object copy may preserve pointer slots through its
layout theorem. Untyped or partial copying requires an explicit reconstruction
proof; partial overwrite invalidates the pointer slot by default.

Pointers returned by an API acquire exactly the access rights, lifetime,
ownership, aliasing, cleanup duties, and thread restrictions promised by that
API's modeled postcondition.

## 3. Authority and loans

The canonical authority states include:

- exclusive read/write ownership;
- shared immutable access;
- atomic shared access with an ordering profile;
- frozen owner fragments while loans exist;
- transferred or unavailable authority.

Every loan has a unique identity. The authoritative state is a finite map from
loan identity to holder, range, rights, lifetime, and conditions. Counts are
derived caches only. Returning one loan consumes that exact identity; exclusive
authority is restored only when the relevant map is empty.

Ordinary concurrent writes to the same byte are prohibited. Conflicting
non-atomic accesses require happens-before ordering. Atomics do not grant
ordinary non-atomic access and must follow the ISA/platform ordering model.

## 4. Initialization and permissions

Initialization is tracked at the granularity required to justify every read.
Typed shapes may summarize byte facts but must expand soundly for partial access,
padding, unions, serialization, or external writes. A write initializes only the
bytes it actually completes.

Read, write, and execute permissions are distinct. Stack storage has explicit
read/write/execute state and provenance tied to a live call frame. Image sections
use standard least privilege. Loader authority to relocate or patch an IAT is a
temporary capability removed before entry.

## 5. Arena allocation

An arena owns one or more upstream blocks and creates child object provenance.
Allocated objects borrow the arena lifetime and cannot be individually freed.
Concurrent allocation authority may be shared when the allocator profile proves
atomic allocation; object access permissions remain separate.

Arena reset/destruction requires exclusive teardown authority and the return of
all live use loans. It processes registered destructor/owned-object obligations,
releases upstream blocks, invalidates all child provenance, and advances an
epoch before reuse. Same-address objects in a new epoch have new provenance.

Moving a typed object within one arena may preserve provenance. Moving across
arenas requires a deep copy, a modeled ownership transfer, or another explicit
proof. Untyped attachment is unsafe until arena identity and lifetime are proved.

## 6. Calls, stacks, and CFG boundaries

Every block entry contract names required registers, stack depth/shape, memory
shape, ghost state, and allowed/disallowed obligations. A call or jump proves
that its outgoing state satisfies the target contract. Stack-frame provenance is
created by the call/entry protocol and destroyed only after all frame loans and
obligations are resolved. Tail calls and nonlocal exits require dedicated
theorems; they are not ordinary returns.

## 7. Concurrent executions

Concurrency is represented by per-context events and explicit relations:

- sequenced-before;
- reads-from;
- per-location modification order;
- synchronizes-with;
- happens-before;
- architecture-specific dependency/order relations.

There is no assumed total global chronology. Data-race freedom is derived from
the event graph and access authority. The common vocabulary is shared across
ISAs; allowed consistency relations are profile-specific. Lock acquire/release,
spawn/join, waits, wakeups, interrupts, signals, GPU/device work, and host/device
visibility declare both authority and causal effects.

### 7.1 Common event vocabulary

A memory event has, at minimum:

```text
event identity
execution context identity and kind
instruction/API cause
location/range and provenance
read/write/read-modify-write/fence/control kind
value read and/or written
atomicity and requested ordering
address space and memory type
scope (thread, process, device, system, profile-specific)
success, partial completion, or fault status
```

Context kinds include thread, interrupt/exception handler, signal/callback,
device queue, shader invocation, DMA engine, loader, and external API agent.
Profiles may add fields but may not reinterpret common ones.

Ordering requests use a portable vocabulary only where it has a proved target
meaning: relaxed, acquire, release, acquire-release, sequentially consistent,
and profile-specific modes. Mapping a high-level order to an ISA/API operation
requires a refinement theorem; unsupported mappings are rejected.

### 7.2 Execution graph well-formedness

An ISA/platform `ConsistencyProfile` defines a predicate over the complete event
graph and a monotonic-prefix/limit discipline. At minimum it constrains:

- sequenced-before to be well formed per context;
- each completed read to select an allowed write or initialization source;
- modification order to order atomic writes per required location domain;
- synchronizes-with edges to follow matched protocol events;
- happens-before to contain required causal closure;
- coherence, visibility, dependency, barrier, and propagation rules;
- faulted or partial events to expose only effects their profile permits.

A modeled execution carries one graph witness; steps monotonically extend it.
Every executable runner prefix proves it can extend to an admitted finite or
infinite graph. Infinite consistency is checked on the limit graph, not inferred
merely because unrelated finite choices were individually plausible.

The common layer does not impose sequential consistency. x86-64, AArch64,
RISC-V, language VMs, GPUs, APIs, and devices supply distinct consistency
predicates over the shared vocabulary. Heterogeneous composition proves that
bridge operations—API synchronization, cache maintenance, queue submission,
fences, or ownership transfer—connect the component relations lawfully.

### 7.3 Data races and access authority

Two events conflict when their live byte ranges overlap, at least one writes,
and they are not both compatible atomic accesses under one profile. A data race
exists when conflicting events from distinct concurrent contexts are unordered
by happens-before and lack an explicitly modeled alternative discipline.

Verified programs prohibit data races. Unique loans prevent ordinary conflicting
authority from being issued; the event-graph theorem covers external agents,
weak memory, and cases where authority alone cannot establish dynamic ordering.
“Thread-safe allocator” authorizes concurrent allocator metadata operations only;
it says nothing about concurrent mutation of returned objects.

### 7.4 Synchronization protocols

Acquire operations may transfer protected memory authority and create a matched
release obligation. Release requires the exact held lock/token, establishes the
profile's causal edge, returns protected authority to the invariant, and
discharges that obligation. Spurious or failed waits transfer no authority unless
their dependent outcome says otherwise.

Multi-lock code carries ordering/ranking demands or another deadlock-progress
argument. Race freedom alone does not establish deadlock freedom. Spawn splits
authority and obligations into a new context; join proves termination and joins
the declared resources. Detach transfers lifecycle responsibility to an explicit
runtime/OS protocol.

Interrupt/signal masking creates restoration obligations and declares exactly
which contexts it excludes. It is not a universal memory fence. Restartable or
partially executed instructions declare the state from which handlers observe
them and the rules for retry.

### 7.5 Address spaces and devices

Provenance includes an address-space identity. CPU virtual memory, physical
memory, device memory, Wasm memories, GPU storage classes, and externally owned
buffers are not interchangeable merely because their offsets match. Mapping,
pinning, sharing, cache maintenance, queue ownership transfer, and unmapping are
typed transitions with obligations.

DMA and GPU agents participate in the event graph. Noncoherent profiles require
explicit visibility/cache operations. Device completion or fence signals create
causal edges only according to their cited API/hardware scopes.

## 8. Faults and audit violations

Architectural faults are modeled events/transitions. Audit violations are a
private append-only diagnostic ledger. They cannot be erased or masked.
`VerifiedProgram` proves the ledger remains empty and that only spec-allowed
fault outcomes occur.

An external contract violation terminates modeled assurance at that boundary:
the prior prefix remains proved, while no post-boundary functional claim is
made. A real model/hardware discrepancy invalidates the affected profile and
must become a validation finding and ratchet gate.

## 9. Versioned extension discipline

The initial implementation may cover one thread and ordinary write-back memory.
Known future cases—weak memory, interrupts, signals, DMA, device memory, GPU
execution, page tables, and hosted processes—are design probes, not a claim that
version 1 is permanently sufficient. Foundational vocabularies are versioned.
Extensions must be conservative for existing profiles or provide explicit
migration/refinement theorems and renewed adversarial review.

No initial choice may make a known target impossible without a migration path,
but Win32 Hello World does not carry proof obligations for unimplemented GPUs,
devices, or operating systems. Unimplemented behavior is rejected by profile
applicability, never modeled as harmless.

## 10. Required proof package

Every memory-capable profile must provide:

- access-descriptor soundness: declared events cover all physical effects;
- range/provenance and initialization preservation;
- permission enforcement and fault fidelity;
- loan-map uniqueness, split/join, transfer, and reclamation laws;
- consistency-graph well-formedness for every admitted execution;
- race-freedom consequences for verified authority/event combinations;
- synchronization and obligation-transfer laws;
- allocator/arena freshness, teardown, and epoch invalidation;
- call-stack/frame lifetime preservation;
- erasure preservation for ghost memory and obligation operations;
- validation metadata connecting the profile to citations and probes.

The profile is not usable by `VerifiedProgram` until this package closes for all
of its admitted operations.
