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
private partial def sensitiveDeclarations
    (declarations : Array (Name × ConstantInfo)) : NameSet :=
  let initial := declarations.foldl (init := {}) fun sensitive declaration =>
    let (name, info) := declaration
    if name == ``Grass.emitProgram ||
        info.type.getUsedConstantsAsSet.contains ``Grass.VerifiedProgram then
      sensitive.insert name
    else
      sensitive
  let rec close (sensitive : NameSet) : NameSet :=
    let expanded := declarations.foldl (init := sensitive) fun found declaration =>
      let (name, info) := declaration
      if found.contains name ||
          !info.getUsedConstantsAsSet.any (fun dependency => found.contains dependency) then
        found
      else
        found.insert name
    if expanded.size == sensitive.size then sensitive else close expanded
  close initial

/-- Audit every project declaration and report direct `VerifiedProgram` roots. -/
elab "#audit_verified_programs" : command => do
  let environment ← getEnv
  let declarations := environment.constants.fold (init := #[]) fun found name info =>
    found.push (name, info)
  let mut roots := #[]
  for (name, info) in declarations do
    if isRootCandidate info && (← liftTermElabM <| producesVerifiedProgram info.type) then
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
  let sensitive := sensitiveDeclarations declarations
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
