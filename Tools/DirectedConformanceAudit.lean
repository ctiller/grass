import Grass.Refinement.ImplementationConformance
import Grass.Refinement.BehaviorCorrespondenceLaws
import Tests.Refinement.ImplementationConformance
import Tests.Refinement.UnclassifiedDeadlock
import Tests.Refinement.Realization
import Lean

/-! Scoped audit of directed conformance, the relative gate, exact compatibility and their test
fixtures. Uses the same project-name normalization, axiom allowlist and compiled
override checks as Tools/AxiomAudit.lean. This does not claim whole-tree coverage
or replace the public certificate/runtime audit. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let publicName := (privateToUserName? name).getD name
    unless (`Grass).isPrefixOf publicName do continue
    count := count + 1
    if info.isUnsafe then throwError "unsafe project declaration: {name}"
    if (Lean.Compiler.getImplementedBy? env name).isSome then
      throwError "compiled replacement: {name}"
    if Lean.isExtern env name then throwError "external replacement: {name}"
    let axioms ← liftCoreM (collectAxioms name)
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} depends on rejected axiom {axiomName}"
  let modules := env.header.moduleNames.filter fun name =>
    (`Grass).isPrefixOf name || (`Tests).isPrefixOf name
  logInfo m!"SCOPED directed conformance audit: {count} project declarations in {modules.size} imported project modules; allowed axioms only, no unsafe declarations or implemented_by/extern replacements. Modules: {modules}"
