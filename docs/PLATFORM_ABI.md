# Platforms, effects, and ABIs

## 1. Effect demands and provider choice

High- and mid-level APIs use law-bearing typeclasses. An abstract class may name
console, filesystem, graphics, process, allocation, or synchronization effects;
a more specific class may demand Vulkan, Metal, Win32, or another provider.

Programs are parameterized by an explicit `ProviderEnv` owned by the
`PlatformPlan`. Effect classes are projections from that environment and are
indexed by a nominal provider key whose type-level identity includes the selected
profile. The exact dictionary/environment value used to elaborate and prove the
high-level program is retained through realization; Grass must not re-run ambient
instance search and obtain a second dictionary for the same key.

Realization proves dictionary identity, not merely equality of key names. An
alternative implementation may enforce uniqueness by construction, but two
instances with different operations or laws for one key must be unrepresentable
in one verified environment.

Intentional multi-provider use requires distinct keys and a compatibility or
noninteraction proof. Platform, ISA, and set of APIs used remain independent
axes joined by plan constraints.

## 2. API model

Every API operation declares:

- complete input domain and memory shape;
- all permitted return values and dependent output-memory states;
- partial completion, interruption, cancellation, and retry behavior;
- register/stack/hidden context requirements at its ABI boundary;
- allocation provenance, access rights, ownership, and lifetime of pointers;
- synchronization, scheduling, and observation events;
- obligations created, discharged, or transferred;
- progress and blocking assumptions;
- failure and environment-violation outcomes;
- citations and validation probes.

Each API profile also proves response adequacy. For every reachable well-formed
request, either at least one response is allowed or the contract explicitly
admits a pending/infinite blocking execution. Its `Allowed` relation covers every
behavior permitted by the cited external contract; it may restrict behavior only
when a cited stronger platform precondition justifies the restriction. A profile
with `Allowed q r := False` and no pending behavior is unusable.

External implementations are trusted relative to this contract, but the
boundary is always modeled and extensively tested.

## 3. ABI profile

An ABI profile is the complete contract between two systems. It includes calling
convention, argument/result placement, clobbers, stack and unwind shape, memory
shape, thread-local/hidden state, callbacks, ghost transfer, obligations,
faults, interruption, cancellation, and progress. Call sites prove the entry
contract; returns and exceptional exits prove their respective postconditions.

Over-approximating clobbers or resource use is acceptable. Omitting a permitted
behavior is unsound.

## 4. Initial Win32 x64 profile

The initial platform API baseline is Win32 x64 with Windows 10 as the minimum
profile. It uses documented Win32 APIs rather than direct system calls. The first
program imports `GetStdHandle`, `WriteFile`, and `ExitProcess` from the provider
set derived from its operations.

The profile includes:

- Microsoft x64 calling convention and complete stack/unwind requirements;
- PE32+ image loading with ASLR enabled;
- section-relative/abstract instruction addresses before layout;
- standard final section permissions;
- loader mapping, relocation, import resolution, IAT patching, and entry transfer;
- partial `WriteFile` results and all documented failure outcomes;
- a zero exit code for specified success and nonzero codes for failure.

The Windows version names the minimum API contract only. It does not assert a
deployment policy. Each API retains its own documented minimum and behavior
citations so later profiles can prove inclusion or restriction.

## 5. Provider families expected

Versioned extension points are intended for Windows, Linux, macOS, bare metal,
WASI, Vulkan, Metal, WebGPU, and SQL data providers. Known target sketches are
reviewed to avoid obvious blockers, but the Win32/x86 foundation is not claimed
permanently sufficient. A genuinely different target may add vocabulary through
a reviewed version and migration/refinement theorems preserving old profiles.
Global coherence constraints belong to the platform plan rather than ambient
instance search.
