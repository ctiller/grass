# Operations, instructions, and ISA profiles

## 1. Open extensibility

Ghost and raw operation sequences use existential packaging behind narrow
interfaces. New ISA instructions, API calls, macros, proof operations, and ghost
protocol operations may be added without editing a closed master sum type.

An operation family supplies only the facets it uses, through separated
interfaces rather than one god class. Mandatory facets include applicability and
step semantics; conditional facets include encoding, decoding, memory events,
control flow, relocation, faults, atomicity, ordering, pretty printing, and
validation metadata.

All reachable operations must close every facet required by their selected
profile. Missing metadata is rejection, not a default empty effect.

## 2. Ghost-bearing layer and erasure

The last verified representation may contain:

- assertions and proof hints;
- obligation and capability manipulation;
- nominal provider evidence;
- typed macros and computed sequences;
- abstract calls and block requirements already connected to realizations;
- ghost state used to simplify local before/after proofs.

Erasure produces only raw instructions, platform call encodings, layout, and
link metadata. Its behavioral-inclusion theorem is oriented from raw executions
to matching ghost executions: erasure may not introduce a raw behavior that the
verified program lacks. It couples initial states and external choices and
covers finite/infinite traces, faults, divergence, terminal states, mandatory
audit events, and projected observations. Proving only that every ghost step has
some raw implementation is insufficient. Ghost operations cannot repair a
physically invalid raw sequence.

## 3. Raw instructions

`RawInstruction profile` carries sufficient information to step and, where
supported, encode the selected operation. Exact encoding choice may be retained
separately from normalized semantics. The primary correctness demand is semantic:
decoded emitted bytes must have the same step relation as the raw program.

An exact encoding type may additionally prove byte round-trip. Redundant prefix,
alias, or width distinctions need not pollute semantic reasoning merely to obtain
syntactic equality.

Each instruction model declares:

- mode, privilege, feature, operand, and encoding applicability;
- register/flag reads, writes, and over-approximated clobbers;
- memory and causal events;
- control successors and indirect-target constraints;
- faults, traps, interrupts, restartability, and partial effects;
- atomicity and memory ordering;
- relocation-bearing fields;
- authoritative citations and validation hooks.

## 4. Macros

Macros are verified computed sequences with before/after contracts. They may
contain CFGs, create obligations, or expose fault/interruption points. They are
not semantically atomic unless a target theorem proves that property. Physical
observability, concurrency, and interruption behavior are always inherited or
explicitly summarized with proof.

## 5. Decoder registry

Decoders register into a global profile registry with enough metadata to
dispatch by ISA, mode, prefix/opcode space, feature set, and priority/conflict
rules. Registration proves nonambiguity or declares an explicitly resolved
overlap. Unknown and ambiguous byte streams return structured errors.

Imported code is decoded into raw instructions and stepped by the same semantics
used for authored code. Direct targets may be found recursively. Indirect
control requires annotations, relocation/symbol evidence, abstract interpretation,
or another proof that every reachable target belongs to the typed CFG.

## 6. Common x86-64

The initial ISA is a common x86-64 profile defined as the reviewed intersection
of Intel and AMD architectural contracts, plus a Win64 execution profile.
Instructions outside the intersection require a vendor/feature refinement.

Every common rule records both vendor citations with document revision and
anchor. Conflicts select the weaker common guarantee, split into refinements, or
exclude the construct. Validation runs separately on Intel and AMD machines.

Primary reference families:

- Intel 64 and IA-32 Software Developer's Manual, especially Volumes 2 and 3:
  https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
- AMD64 Architecture Programmer's Manual, Volumes 1-5:
  https://docs.amd.com/v/u/en-US/40332_4.09_APM_PUB

The profile/refinement mechanism is a versioned extension point intended for x86
variants, ARM, RISC-V, Wasm, SPIR-V, WGSL, Verilog, and other instruction-like
targets. A new target may conservatively extend foundational vocabulary after
review and must provide migration/refinement theorems for existing profiles. The
initial interface is not presumed permanently sufficient for unlike targets.
