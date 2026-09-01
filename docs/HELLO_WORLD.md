# Milestone 1: verified Win32 x64 Hello World

The complete annotated proof proposal is [SPIKE_1.md](SPIKE_1.md). This file is
the concise milestone checklist; the spike document owns the proposed source,
lowering, and certificate shape.

The first milestone proves the entire architecture with the smallest useful
external program. It is incomplete until every item below is connected.

## Specification

The high-level Lean specification requests one fixed byte string on the standard
output stream. It accepts every outcome allowed by the portable
`Console.writeStdout` contract.
Success means the full string was written and terminal status is zero. Every
noncontinuable failure has one public `.failure` outcome, permits only a prefix
of the requested bytes, and has status one. Standard-output unavailable,
write failure, and zero progress remain distinct only in the complete audit
trace. A product needing public diagnostic distinctions selects another policy.

Partial writes are handled until complete or failure. A successful write of a
strictly positive prefix decreases the remaining-length measure. A successful
zero-byte write is handled as an explicit no-progress failure unless a stronger
provider contract supplies a reviewed progress rule. The theorem quantifies
over all handle values, return values, byte counts, failure codes, scheduling
choices, load bases, and other permitted environment/oracle responses.

Termination is conditional on the fixed portable `environmentResponsive`
predicate: under a coherent abstract branching strategy, every reachable
frontier settles on every compatible maximal continuation and each terminal
frontier produces its declared observation. The Win32 plan must exhibit an
inhabited concrete branching provider/scheduler strategy satisfying all its
assumptions and map that same strategy through an explicit projection and
complete-history-set refinement coupling to the portable predicate. Conditional
termination quantifies over every compatible conforming execution. A blocked
redirected pipe is a declared
environmental frontier and may wait forever when that premise is absent.
`ExitProcess` is not assumed to return; its terminal protocol proves status
preservation/reflection/distinguishability and terminal resource disposition.
Safety remains unconditional; liveness does not silently assume a reader or
friendly console device.

## Realization

The Win32 providers separately cover every modeled physical response and prove
that each conforming response refines a portable console outcome.

- Platform/API profile: Win32 x64, Windows 10 baseline.
- ISA: common x86-64 profile with Intel and AMD citations.
- Binary: ASLR-enabled PE32+.
- APIs: `GetStdHandle`, `WriteFile`, `ExitProcess` using documented Win32 calls.
- Product profile: explicitly synchronous-standard-output-only; inherited
  overlapped handles are unsupported until an adaptive provider is realized.
  This is explicitly the architecture-validation artifact, not Grass's default
  production Windows standard-output implementation. It is shippable only when
  the applicability constraint is declared in artifact metadata. The eventual
  general provider adapts synchronous/overlapped operations behind the same
  byte-flow contract.
- Imports: derived exactly from realized operations.
- Entry point: verified loader-entry ABI context.
- Sections: standard least-privilege permissions.
- Layout: abstract RIP/section-relative proof followed by relocation.
- Unwind: generated `.pdata`/`.xdata` consistent with the realized prologue.

The spike uses the unique standard sequential realizer for the console
specification plus ordinary dependent Win32 API contracts. It does not ask the author to
describe a virtual process population or Hoare channels. The library
`SequentialAdapter` elaborates the equivalent degenerate process network in the
same universal process algebra used by the server and cube; that adapter is not
precious or author-maintained.
The assembly write loop is checked against `DirectWriteInvariant`.

## Required proof chain

1. The minimal portable specification states success/failure, numeric terminal
   status, safety, and progress without platform representation details; an
   optional high-level program route proves satisfaction separately.
2. The library's selected `DirectProgramRealizes` witness proves the extensional relational console program
   non-vacuously realizes the precious spec for all admitted inputs/results;
   `SequentialAdapter` then produces the canonical `ProcessPlanRealizes` proof.
3. Win32 provider realization derives a platform contract from that route for all
   permitted results, exports its context requirements, proves concrete
   responsiveness implies the fixed portable predicate, and constructs the
   terminal-status protocol laws.
4. A generated or authored typed CFG refines that platform contract and satisfies
   every block, stack, memory, ABI, and obligation contract.
5. Instruction lowering and ghost erasure preserve semantics.
6. Every permitted execution prefix is memory/race/fault safe.
7. Internal work between API frontiers terminates; every positive partial write
   strictly reduces the remaining length; zero progress takes an explicit
   failure branch; nonterminal calls use the named responsiveness assumption;
   and `ExitProcess` uses its nonreturning terminal-completion contract.
8. PE writer/reader laws and canonicalization hold for the represented subset.
9. Abstract loader connection establishes mapped code, imports, relocations,
   permissions, unwind data, and entry state.
10. Decoded loaded code has the step relation used by the verification proof.
11. Physical probes run the artifact on reviewed Intel and AMD Windows hosts.

## Acceptance

The milestone is accepted only when `emitProgram helloVerified` yields bytes
that parse as the modeled PE, execute successfully on responsive validation
hosts, emit the
specified bytes, and satisfy the complete proof chain without axioms or
`native_decide`. Execution results demonstrate the artifact but do not replace
the proof.
