# Obligations and dispositions

An obligation is a linear ghost resource stating that its holder must perform a
future action or transfer responsibility under a named protocol.

## 1. Form

An obligation has a unique identity, kind, owner/context, precondition, accepted
discharge events, transfer rules, cancellation/fault behavior, and terminal
dispositions. Payloads are existential so new instruction, API, ABI, allocator,
lock, transaction, interrupt, and device protocols can extend the ledger.

Examples include unlock-after-lock, restore-interrupt-state, release allocation,
finish/abort transaction, join/detach thread, restore ABI state, complete partial
I/O, and return borrowed authority.

At process level, Hoare channel sends and child-process lifecycle transitions
are obligation-transfer boundaries. A send postcondition names which obligations
remain with the sender, move with the exact message occurrence, or are created
for supervision/cancellation. Receive consumes that occurrence and reconstructs
the receiver's exact ledger. Driver lowering proves the physical
queue/callback/API path implements the same transfer.

## 2. Ledger law

Every semantic transition states how it transforms the ledger. It may preserve,
create, discharge, split, join, or transfer obligations only through the owning
protocol theorem. Dropping, duplicating, or fabricating obligations is forbidden.

Ledger effects are sequenced at explicit commit points in the operation's
ordered effect frontier. A delta whose commit point precedes a later fault
remains visible; a delta scheduled at or after an access that faults is not
applied. In particular, one instruction-wide delta scheduled after all accesses
does not apply when an earlier access fails. A fault may create a distinct
fault-handling obligation only through the fault protocol's own typed delta and
applicability theorem. There is no generic recovery fold that guesses whether a
failed operation created, discharged, or abandoned a duty.

The frontier is closed under protocol-declared **effect/obligation pairing**.
When a committed effect creates or transfers custody that carries a duty, the
effect and the delta installing that duty belong to one indivisible commit
group. Likewise, an effect whose protocol meaning discharges a duty and the
corresponding discharge delta commit together. A visible prefix may contain
both members or neither; it may not strand acquired authority without its
release duty, nor consume the duty while leaving the protected state held.
Ghost sequencing may therefore coincide with the concrete effect's
linearization point even when no separately emitted instruction exists there.
This is a protocol theorem, not a convention inferred by the common stepper.

The memory/operation proof package relates each possible fault frontier to the
exact committed ledger prefix, proves that prefix closed under every declared
pairing, and proves every retained or fault-created delta well formed and
applicable. It includes discriminating fixtures for faults before, at, and
after a ledger commit point; a negative fixture in which an acquiring write is
visible but its release duty is scheduled later must be rejected. Positive
controls commit both halves together and expose neither half when a fault lies
before their group. Merely showing that one successful path updates the ledger
is insufficient.

CFG block contracts list obligations allowed and forbidden on entry and exit.
Calls and jumps prove ledger compatibility. Macros may introduce obligations and
must expose their interruption/fault/concurrency interactions; constructs such
as `cli`/`sti` or lock/unlock cannot be silent straight-line conveniences.

## 3. Terminal dispositions

Every obligation at a terminal edge has one profile-approved disposition:

- `discharged` — the required action occurred;
- `transferred` — a named live owner accepted it;
- `teardownAdopted` — the OS/runtime teardown contract assumes it;
- `aborted` — the protocol's failure branch was performed;
- `abandonedUnknown` — failure permits loss of knowledge, explicitly reflected
  in the program result/specification.

Process exit may transfer virtual memory, handles, and similar resources to a
modeled OS teardown contract. It cannot claim that external invariants such as a
database transaction were restored unless the external profile promises that.
Successful exit must not leave external obligations in an abnormal disposition.
Failure may use `aborted` or `abandonedUnknown` only when its specification
accepts that outcome.

The verified theorem is indexed by the specification and its result/observation
mapping. For every terminal execution it connects the concrete final ledger and
each disposition to the exact declared success, failure, abort, or unknown
result. A platform profile's permission to abandon an obligation does not by
itself prove that the program specification reports that abandonment.

## 4. Emergency failure

An expected failure retains all safety and failure-postcondition proofs. An
environment contract violation preserves only the proved prefix and invokes a
minimal modeled termination path if its independent prerequisites remain valid.
Discovering that the CPU/platform model is false is a profile/TCB failure, not a
semantic mechanism for discharging obligations.
