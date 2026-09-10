# Lowering recipe removal

The lowering deletion removes the mandatory `SourceWitness` loop/guard aggregate,
`Assembly.WriteAllLoopSource`, `Assembly.WriteAllGuardSource`, and the fixed
register, instruction-sequence, local-name, and branch-label schemas in
`Refinement.Console.WriteAll*`, `WriteFileLoad`, `WriteFileResume`,
`WriteFileCountAddress`, and `WriteFileCountEntry`.

Their tests and unused downstream count/static-entry/finalization wrappers are
also removed. The generic fragments inside those wrappers had no surviving
general consumer. `SourceWitness` is deleted rather than duplicated as another
structural constructor: the existing frontend construction path already composes
the source and image producers.

The retained `WriteFileSourceEntry.prepareCall?` checks arbitrary incoming CALL
arguments through the existing ABI and handoff producers. Generic source fetch,
frame-memory execution, checked CALL dispatch, provider-history folds, and return
completion remain unchanged. None requires the `transferred` local, the
`write_head` label, or the Hello register allocation and instruction schedule.

The authored spike and its invariant annotation are unchanged. Removed recipes
are not relocated into a hand-maintained program companion or replaced with new
author obligations. The required endpoint remains generic semantic verification
conditions and proof synthesis behind `verify_assembly`, with generated proof
terms checked by the kernel. This deletion does not implement that endpoint.

## Validation boundary

The retained generic construction, ISA/source, CALL, service-history, return, and
incoming-argument modules are checked separately from whole-certificate work.
The broad `lake build Grass Tests` attempt encountered existing elaboration errors
in `Grass.Certificate` involving `ProgramBehavior`, `BehaviorRefinement`, and
resource-model parameters; it was stopped rather than reported as passing.

The former frontend prefix template and slicing gate are separately owned
deletions. They are not a replacement acceptance gate for this checkpoint.
Complete verification of the unchanged authored program remains incomplete until
generic VC generation and kernel-checked proof synthesis establish its behavior.
