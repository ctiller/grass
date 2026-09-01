# Milestone 1: verified Win32 x64 Hello World

The first milestone proves the entire architecture with the smallest useful
external program. It is incomplete until every item below is connected.

## Specification

The high-level Lean specification requests one fixed byte string on the standard
output stream. It accepts every Win32 response allowed by the modeled APIs.
Success means the full string was written and the process exits with code zero.
Failure is explicit, noncontinuable, and exits with a specified nonzero code.

Partial writes are handled until complete or failure. A successful write of a
strictly positive prefix decreases the remaining-length measure. A successful
zero-byte write is handled as an explicit no-progress failure unless a stronger
provider contract supplies a reviewed progress rule. The theorem quantifies
over all handle values, return values, byte counts, failure codes, scheduling
choices, load bases, and other permitted environment/oracle responses.

Termination is conditional on named Win32 progress assumptions. Every
nonterminal blocking request, including `WriteFile`, eventually produces a
modeled response. A blocked redirected pipe is a declared environmental frontier
and may wait forever when that assumption is absent. `ExitProcess` is not assumed
to return; its separate terminal-completion contract says that an admitted call
reaches the declared terminal process state. Safety remains unconditional;
liveness does not silently assume a reader or friendly console device.

## Realization

- Platform/API profile: Win32 x64, Windows 10 baseline.
- ISA: common x86-64 profile with Intel and AMD citations.
- Binary: ASLR-enabled PE32+.
- APIs: `GetStdHandle`, `WriteFile`, `ExitProcess` using documented Win32 calls.
- Imports: derived exactly from realized operations.
- Entry point: verified process-root ABI context.
- Sections: standard least-privilege permissions.
- Layout: abstract RIP/section-relative proof followed by relocation.
- Unwind: generated `.pdata`/`.xdata` consistent with the realized prologue.

## Required proof chain

1. High-level program satisfies its success/failure and progress specification.
2. Win32 provider realization refines the high-level effects for all results.
3. Typed CFG satisfies every block, stack, memory, ABI, and obligation contract.
4. Instruction lowering and ghost erasure preserve semantics.
5. Every permitted execution prefix is memory/race/fault safe.
6. Internal work between API frontiers terminates; every positive partial write
   strictly reduces the remaining length; zero progress takes an explicit
   failure branch; nonterminal calls use the named responsiveness assumption;
   and `ExitProcess` uses its nonreturning terminal-completion contract.
7. PE writer/reader laws and canonicalization hold for the represented subset.
8. Abstract loader connection establishes mapped code, imports, relocations,
   permissions, unwind data, and entry state.
9. Decoded loaded code has the step relation used by the verification proof.
10. Physical probes run the artifact on reviewed Intel and AMD Windows hosts.

## Acceptance

The milestone is accepted only when `emitProgram helloVerified` yields bytes
that parse as the modeled PE, execute successfully on responsive validation
hosts, emit the
specified bytes, and satisfy the complete proof chain without axioms or
`native_decide`. Execution results demonstrate the artifact but do not replace
the proof.
