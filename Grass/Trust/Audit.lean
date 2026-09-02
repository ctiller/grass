import Lean
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Grass.Verify.VerifiedProgram

/-!
# VerifiedProgram trust-root audit

The command inspects elaborated declarations in the Lean environment. It does
not guess roots from source syntax: it discovers direct `VerifiedProgram`
producers from their types, follows the transitive dependency closure of all
certificate-bearing and emission-consuming declarations across imported
modules, and audits every declaration originating in a Grass library or test
module. A wrapper cannot escape merely because its own result type is not
headed by `VerifiedProgram` or its module uses an unrelated namespace.
-/

namespace Grass.Trust

open Lean Meta Elab Command

private def isRootCandidate : ConstantInfo -> Bool
  | .axiomInfo _ => true
  | .defnInfo _ => true
  | .opaqueInfo _ => true
  | _ => false

private def allowedAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

private def producesVerifiedProgram (type : Expr) : MetaM Bool :=
  withTransparency .all do
    forallTelescopeReducing type fun _ result => do
      let reduced ← whnf result
      return reduced.getAppFn.constName? == some ``Grass.VerifiedProgram

private def isProjectModule (moduleName : Name) : Bool :=
  (`Grass).isPrefixOf moduleName || (`Tests).isPrefixOf moduleName

/-- A declaration from an imported Grass/Test module, or from the current file
that invoked the command. The latter case is what makes negative probes and
top-level declarations outside the conventional namespaces fail closed. -/
private def isProjectDeclaration (environment : Environment) (name : Name) : Bool :=
  if name.isInternal then
    false
  else
    match environment.getModuleIdxFor? name with
    | none => true
    | some moduleIndex =>
        match environment.header.moduleNames[moduleIndex.toNat]? with
        | none => false
        | some moduleName => isProjectModule moduleName

/-- Declarations whose type or implementation depends on certificate authority
or verified emission, closed transitively over the whole imported environment.
This is deliberately module-name agnostic so downstream wrappers are audited. -/
private def sensitiveDeclarations
    (environment : Environment)
    (declarations : Array (Name × ConstantInfo)) : Std.HashSet Name :=
  Id.run do
    let verifiedModuleIndex := environment.getModuleIdxFor? ``Grass.VerifiedProgram
    -- Imported modules are indexed in dependency order. A declaration from a
    -- strictly earlier module cannot mention VerifiedProgram; current-module
    -- declarations have no index yet and must always be included.
    let candidates := declarations.filter fun declaration =>
      match verifiedModuleIndex, environment.getModuleIdxFor? declaration.1 with
      | some verifiedIndex, some declarationIndex =>
          verifiedIndex.toNat ≤ declarationIndex.toNat
      | _, _ => true
    let mut seeds : Std.HashSet Name :=
      Std.HashSet.emptyWithCapacity (capacity := candidates.size)
    let mut reverseDependencies : Std.HashMap Name (Array Name) :=
      Std.HashMap.emptyWithCapacity (capacity := candidates.size)
    for (name, info) in candidates do
      if name == ``Grass.emitProgram ||
          info.type.getUsedConstantsAsSet.contains ``Grass.VerifiedProgram then
        seeds := seeds.insert name
      for dependency in info.getUsedConstantsAsSet do
        let dependents := reverseDependencies.get? dependency |>.getD #[]
        reverseDependencies := reverseDependencies.insert dependency (dependents.push name)
    let mut sensitive : Std.HashSet Name := seeds
    let mut pending : Array Name := seeds.toArray
    while let some name := pending.back? do
      pending := pending.pop
      if let some dependents := reverseDependencies.get? name then
        for dependent in dependents do
          unless sensitive.contains dependent do
            sensitive := sensitive.insert dependent
            pending := pending.push dependent
    return sensitive

/-- Audit every project declaration and report direct `VerifiedProgram` roots. -/
elab "#audit_verified_programs" : command => do
  let environment ← getEnv
  let declarations := environment.constants.fold (init := #[]) fun found name info =>
    found.push (name, info)
  let mut roots := #[]
  for (name, info) in declarations do
    if !name.isInternal && isRootCandidate info &&
        (← liftTermElabM <| producesVerifiedProgram info.type) then
      roots := roots.push (name, info)
  if roots.isEmpty then
    throwError "trust audit found no concrete VerifiedProgram declarations"
  -- Root discovery is intentionally global: downstream users may invoke the
  -- command from modules outside the repository's namespace conventions.
  for (name, info) in roots do
    if info.isUnsafe then
      throwError "VerifiedProgram root '{name}' is unsafe"
    let axioms ← collectAxioms name
    let rejected := axioms.filter fun axiomName => !allowedAxiom axiomName
    unless rejected.isEmpty do
      throwError "VerifiedProgram root '{name}' uses rejected axioms: {rejected.toList}"
  let sensitive := sensitiveDeclarations environment declarations
  for (name, info) in declarations do
    unless sensitive.contains name do continue
    if info.isUnsafe then
      throwError "certificate-sensitive declaration '{name}' is unsafe"
    let axioms ← collectAxioms name
    let rejected := axioms.filter fun axiomName => !allowedAxiom axiomName
    unless rejected.isEmpty do
      throwError "certificate-sensitive declaration '{name}' uses rejected axioms: \
        {rejected.toList}"
  let projectDeclarations := declarations.filter fun candidate =>
    isProjectDeclaration environment candidate.1
  for (name, info) in projectDeclarations do
    if info.isUnsafe then
      throwError "project declaration '{name}' is unsafe"
    let axioms ← collectAxioms name
    let rejected := axioms.filter fun axiomName => !allowedAxiom axiomName
    unless rejected.isEmpty do
      throwError "project declaration '{name}' uses rejected axioms: {rejected.toList}"
  logInfo m!"VerifiedProgram trust audit passed for {roots.size} concrete root(s), \
    {sensitive.size} certificate-sensitive declaration(s), and \
    {projectDeclarations.size} project declaration(s): \
    {roots.map (fun root => root.1) |>.toList}"

end Grass.Trust
