import Lean
import Lean.Util.CollectAxioms
import Grass.Verify.VerifiedProgram

/-!
# VerifiedProgram trust-root audit

The command inspects elaborated declaration types in the Lean environment. It
does not guess roots from source syntax, and it audits exact fully qualified
constants including factories whose result is a `VerifiedProgram`.
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

/-- Audit every concrete `VerifiedProgram` producer visible in the environment. -/
elab "#audit_verified_programs" : command => do
  let environment ← getEnv
  let candidates := environment.constants.fold (init := #[]) fun found name info =>
    if isRootCandidate info && !name.toString.endsWith "._flat_ctor" then
      found.push (name, info)
    else found
  let mut roots := #[]
  for (name, info) in candidates do
    if ← liftTermElabM <| producesVerifiedProgram info.type then
      roots := roots.push (name, info)
  if roots.isEmpty then
    throwError "trust audit found no concrete VerifiedProgram declarations"
  for (name, info) in roots do
    if info.isUnsafe then
      throwError "VerifiedProgram root '{name}' is unsafe"
    let axioms ← collectAxioms name
    let rejected := axioms.filter fun axiomName => !allowedAxiom axiomName
    unless rejected.isEmpty do
      throwError "VerifiedProgram root '{name}' uses rejected axioms: {rejected.toList}"
  logInfo m!"VerifiedProgram trust audit passed for {roots.size} concrete root(s): \
    {roots.map (fun root => root.1) |>.toList}"

end Grass.Trust
