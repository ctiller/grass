import Lean
import Lean.Util.CollectAxioms
import Grass.Verify.VerifiedProgram

/-!
# VerifiedProgram trust-root audit

The command inspects elaborated declarations in the Lean environment. It does
not guess roots from source syntax: it discovers direct `VerifiedProgram`
producers from their types and audits every declaration originating in a Grass
library or test module. The broader project-module pass prevents a wrapped
certificate or a downstream byte-producing definition from escaping the trust
boundary merely because its result type is not headed by `VerifiedProgram`.
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

/-- Audit every project declaration and report direct `VerifiedProgram` roots. -/
elab "#audit_verified_programs" : command => do
  let environment ← getEnv
  let declarations := environment.constants.fold (init := #[]) fun found name info =>
    if !name.toString.endsWith "._flat_ctor" then
      found.push (name, info)
    else found
  let mut roots := #[]
  for (name, info) in declarations do
    if isRootCandidate info && (← liftTermElabM <| producesVerifiedProgram info.type) then
      roots := roots.push (name, info)
  if roots.isEmpty then
    throwError "trust audit found no concrete VerifiedProgram declarations"
  let projectDeclarations := declarations.filter fun candidate =>
    isProjectDeclaration environment candidate.1
  for (name, info) in projectDeclarations do
    if info.isUnsafe then
      throwError "project declaration '{name}' is unsafe"
    let axioms ← collectAxioms name
    let rejected := axioms.filter fun axiomName => !allowedAxiom axiomName
    unless rejected.isEmpty do
      throwError "project declaration '{name}' uses rejected axioms: {rejected.toList}"
  logInfo m!"VerifiedProgram trust audit passed for {roots.size} concrete root(s) \
    and {projectDeclarations.size} project declaration(s): \
    {roots.map (fun root => root.1) |>.toList}"

end Grass.Trust
