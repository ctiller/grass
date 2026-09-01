# Ratified design decisions

This file records decisions already accepted for the initial implementation.
Normative owners take precedence if wording is later incorporated there.

1. `emitProgram : VerifiedProgram spec -> ByteArray` is the verified gate.
2. Functional refinement and platform/ISA safety are separate certificate fields.
3. Normative execution semantics is relational; an oracle-driven runner selects
   replayable modeled executions and proves soundness. `PermittedExecution`
   means the conforming member of the modeled-execution partition.
4. Safety is universal over finite prefixes; progress, productivity, conditional
   termination, and unconditional termination are separate demands.
5. Reactive CFG cycles must decrease or universally cross a law-bearing frontier
   that transfers agency or has an independent specification-productivity proof.
6. Requirements are separate theorem demands and remain separated when possible.
7. Ghost-bearing operations lower through proved erasure to an unsafe raw layer.
8. Operations and obligations use existential packaging for open extensibility.
9. Memory uses generative hierarchical provenance, shadow pointer provenance,
   initialization, permissions, and a sealed access chokepoint.
10. Pointer recovery from integers and provenance preservation by untyped copies
    require additional proofs; typed operations may supply them automatically.
11. Borrow sharing uses authoritative unique loan identities; counts are derived.
12. Ordinary conflicting parallel writes are prohibited; atomics and ordering are
    separately modeled.
13. Obligations have explicit terminal dispositions, including unknown/abandoned
    failure where the specification permits it.
14. Provider demands use typeclasses projected from an explicit provider
    environment; the platform plan retains the exact dictionaries used upstream
    and ghost-propagates their identities.
15. The initial ISA is a dual-cited common x86-64 intersection with Intel and AMD
    refinements and separate validation.
16. The initial platform profile is Win32 x64 with Windows 10 as API baseline and
    documented APIs rather than direct syscalls.
17. The initial artifact is ASLR-enabled PE32+ with abstract RIP, relocations,
    derived imports, standard permissions, and unwind metadata.
18. Windows loading is an abstract proved transition including IAT patching; the
    actual loader remains a tested platform trust item.
19. Every writer has a reader and proves writer round-trip plus canonicalization
    for accepted inputs. Format-specific connection properties are additional.
20. Exact x86 syntactic round-trip may be weakened to semantic encode/decode
    equivalence when exactness harms instruction reasoning.
21. All instruction/API behavior has vendor/standard citations, review anchors,
    fuzzers, probes, and a per-profile trust ledger.
22. External libraries are trusted implementations only behind fully modeled and
    tested boundaries.
23. Proofs use the kernel; `native_decide` is prohibited and execution is not a
    proof. Universally quantified `bv_decide` is allowed.
24. The final certificate proves loaded behavior inclusion from the exact emitted
    bytes back to the ghost program across finite/infinite executions and faults.
25. Foundational extension points are versioned and migration-proved; version 1
    is tested against known targets but is not promised permanently sufficient.
26. Pure `Vec α` is the fundamental finite ordered array and `ByteArray` is the
    early public name for `Vec Byte`; physical `OwnedVec` carries distinct
    allocation identity and proves `Represents` rather than sharing extensional
    equality with the logical value.
27. Every verified artifact proves non-vacuous loadability for all admissible
    bases/import environments; those domains have independent inhabitants and
    every loader result is a valid initial state. Every profile proves nonempty
    execution and response-or-pending domains.
28. Environment-contract violations receive assurance only through the maximal
    matched safe prefix before the first violation; no post-violation functional
    or cleanup claim is made.
29. Physical vectors separate stable `vecId` from generative `bufferId`;
    reallocation preserves the former and existentially returns a fresh latter.
    Capacity, allocation failure, mutable loans, and provenance belong only to
    `OwnedVec`, never pure `Vec`.
30. Every valid initial state has a modeled execution; a terminal initial state
    contributes an explicit zero-step conforming execution with its result and
    terminal resources.
31. Verified theorems receive a transitive axiom audit across all dependencies;
    only exact reviewed Lean logical-foundation constants are allowed.
32. Standard-library dependencies are stratified as `Core -> Std.Logical ->
    Semantics/Memory/Obligation -> Std.Owned`; lower ownership models never
    import their physical container specializations.

## Explicitly rejected shortcuts

- bolting memory safety on after an instruction library exists;
- treating ghost streams and raw streams as peer verified representations;
- using one sharing count without loan identities;
- treating API failure as impossible or as an unconstrained no-op;
- choosing providers through ambient global instance search;
- calling Windows syscalls directly for the initial user program;
- disabling ASLR to simplify proofs;
- proving a semantic instruction list while emitting unconnected bytes;
- accepting undecodable indirect control flow as safe;
- relying on emulator/fuzzer agreement as proof;
- silently considering obligations discharged on process failure.
