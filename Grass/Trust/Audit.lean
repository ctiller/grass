import Lean
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
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
module. It also follows downstream runtime dependencies and rejects unverified
`implemented_by` or `extern` replacements outside the declared upstream
toolchain boundary. Module cohorts and recorded regular compiler dependencies
make scoped `csimp` substitutions part of that audit even after their attribute
state expires. A wrapper cannot escape merely because its own result type is not
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

/-
The exact import-DAG closure of the pinned toolchain roots. Module names or
numeric import order are not provenance: an unrelated helper may be loaded
before `VerifiedProgram`, and a project could choose a toolchain-looking
namespace. Only actual dependencies of these exact roots are in this boundary.
-/
private def trustedToolchainModules (environment : Environment) : Std.HashSet Name :=
  Id.run do
    let mut trusted : Std.HashSet Name := {}
    let mut pending : Array Name := #[`Init, `Lean, `Std]
    for root in pending do
      trusted := trusted.insert root
    while let some moduleName := pending.back? do
      pending := pending.pop
      if let some moduleIndex := environment.getModuleIdx? moduleName then
        if let some moduleData := environment.header.moduleData[moduleIndex.toNat]? then
          for imported in moduleData.imports do
            unless trusted.contains imported.module do
              trusted := trusted.insert imported.module
              pending := pending.push imported.module
    return trusted

/-
Declarations in the fail-closed runtime dependency cone of certificate-sensitive
code. Each reachable non-toolchain module contributes its whole declaration
cohort and every recorded non-meta compiler dependency module. This deliberately
uses the persistent module record rather than the current `csimp` map: scoped or
overwritten compiler substitutions can already have affected generated code when
their active attribute entry is no longer visible. Ordinary declaration edges
then close the participating cohorts transitively.
-/
private def runtimeDependencyDeclarations
    (environment : Environment)
    (declarations : Array (Name × ConstantInfo))
    (sensitive : Std.HashSet Name)
    (trustedModules : Std.HashSet Name) : Std.HashSet Name :=
  Id.run do
    let currentModuleKey := `_grassTrustAuditCurrentModule
    let moduleOf := fun name =>
      match environment.getModuleIdxFor? name with
      | none => currentModuleKey
      | some moduleIndex =>
          environment.header.moduleNames[moduleIndex.toNat]?.getD currentModuleKey
    let mut declarationByName : Std.HashMap Name ConstantInfo :=
      Std.HashMap.emptyWithCapacity (capacity := declarations.size)
    let mut declarationsByModule : Std.HashMap Name (Array Name) := {}
    for (name, info) in declarations do
      declarationByName := declarationByName.insert name info
      let moduleName := moduleOf name
      let cohort := declarationsByModule.get? moduleName |>.getD #[]
      declarationsByModule := declarationsByModule.insert moduleName (cohort.push name)
    let mut reachable := sensitive
    let mut pendingDeclarations := sensitive.toArray
    let mut pendingModules : Array Name :=
      sensitive.toArray.map moduleOf
    let mut expandedModules : Std.HashSet Name := {}
    while !pendingDeclarations.isEmpty || !pendingModules.isEmpty do
      if let some moduleName := pendingModules.back? then
        pendingModules := pendingModules.pop
        unless expandedModules.contains moduleName || trustedModules.contains moduleName do
          expandedModules := expandedModules.insert moduleName
          for name in declarationsByModule.get? moduleName |>.getD #[] do
            unless reachable.contains name do
              reachable := reachable.insert name
              pendingDeclarations := pendingDeclarations.push name
          if moduleName == currentModuleKey then
            -- The persistent extension does not expose current-module entries.
            -- If current declarations are sensitive, conservatively include all
            -- untrusted imports; imported modules below retain precise records.
            for importedModule in environment.header.moduleNames do
              unless trustedModules.contains importedModule do
                pendingModules := pendingModules.push importedModule
          else if let some moduleIndex := environment.getModuleIdx? moduleName then
            if let some moduleData := environment.header.moduleData[moduleIndex.toNat]? then
              -- Importing a module runs its initializers even when no declaration
              -- in the importing module refers to them.
              for imported in moduleData.imports do
                unless trustedModules.contains imported.module do
                  pendingModules := pendingModules.push imported.module
            for extraUse in getExtraModUses environment moduleIndex do
              if !extraUse.isMeta && !trustedModules.contains extraUse.module then
                pendingModules := pendingModules.push extraUse.module
      else if let some name := pendingDeclarations.back? then
        pendingDeclarations := pendingDeclarations.pop
        let moduleName := moduleOf name
        unless trustedModules.contains moduleName do
          pendingModules := pendingModules.push moduleName
          if let some info := declarationByName.get? name then
            for dependency in info.getUsedConstantsAsSet do
              if declarationByName.contains dependency && !reachable.contains dependency then
                reachable := reachable.insert dependency
                pendingDeclarations := pendingDeclarations.push dependency
    return reachable

/-- Audit one supplied seed set through the runtime/module closure. -/
private def auditRuntimeDependencies
    (environment : Environment)
    (declarations : Array (Name × ConstantInfo))
    (seeds : Std.HashSet Name) : CommandElabM (Std.HashSet Name) := do
  let trustedModules := trustedToolchainModules environment
  let runtimeDependencies :=
    runtimeDependencyDeclarations environment declarations seeds trustedModules
  for name in runtimeDependencies do
    if let some moduleIndex := environment.getModuleIdxFor? name then
      if let some moduleName := environment.header.moduleNames[moduleIndex.toNat]? then
        if trustedModules.contains moduleName then
          continue
    if let some implementation := Compiler.getImplementedBy? environment name then
      throwError "runtime dependency '{name}' uses unverified implemented_by replacement \
        '{implementation}'"
    if (getExternAttrData? environment name).isSome then
      throwError "runtime dependency '{name}' uses an unverified extern implementation"
    if let some info := environment.find? name then
      if info.isUnsafe then
        throwError "runtime dependency '{name}' is unsafe"
      let axioms ← collectAxioms name
      let rejected := axioms.filter fun axiomName => !allowedAxiom axiomName
      unless rejected.isEmpty do
        throwError "runtime dependency '{name}' uses rejected axioms: {rejected.toList}"
  return runtimeDependencies

/-
Focused diagnostic used by adversarial fixtures. It audits only the runtime and
module closure of the named declaration; the repository gate remains
`#audit_verified_programs`, which additionally discovers roots and audits all
project declarations.
-/
elab "#audit_runtime_dependencies " declaration:ident : command => do
  let environment ← getEnv
  let name := declaration.getId
  unless environment.contains name do
    throwError "unknown runtime audit seed '{name}'"
  let declarations := environment.constants.fold (init := #[]) fun found name info =>
    found.push (name, info)
  let seeds := (Std.HashSet.emptyWithCapacity (capacity := 1)).insert name
  let runtimeDependencies ← auditRuntimeDependencies environment declarations seeds
  logInfo m!"runtime dependency audit passed for '{name}' across \
    {runtimeDependencies.size} declaration(s)"

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
  let runtimeDependencies ←
    auditRuntimeDependencies environment declarations sensitive
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
    {sensitive.size} certificate-sensitive declaration(s), \
    {runtimeDependencies.size} downstream runtime dependency declaration(s), and \
    {projectDeclarations.size} project declaration(s): \
    {roots.map (fun root => root.1) |>.toList}"

end Grass.Trust
