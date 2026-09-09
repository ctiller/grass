import Grass.Semantics.SpecProcess
import Grass.Semantics.Environment
import Std.Data.String.ToNat

namespace Grass

namespace AuthoredDemand

/-- Suite-local diagnostic identity. Different roots can share these names;
`DemandCertificateFamily` retains the full family as its proof index. -/
def identity (position : Nat) : RequirementKey :=
  ⟨⟨"Grass.SpecProcess", Nat.repr position⟩⟩

theorem identity_injective : Function.Injective identity := by
  intro a b equal
  exact Nat.repr_injective (congrArg (fun key => key.id.localName) equal)

/-- Positional identities are computed from the captured ordered suite. -/
def family (rows : List AuthoredDemand) : DemandFamily where
  Key := Fin rows.length
  keys := List.finRange _
  complete := List.mem_finRange
  unique := List.nodup_finRange _
  identity := fun key => identity key.val
  identityInjective := fun _ _ equal => Fin.ext (identity_injective equal)
  kind := fun key => (rows[key]).kind
  statement := fun key => (rows[key]).statement

end AuthoredDemand

namespace SpecProcess
variable {R : Type} [Resource.ResourceModel R] {resources : R}

/-- Unconditional termination includes every terminal, infinite, and waiting behavior. -/
def UnconditionallyTerminates {Outcome : Type} (model : BehaviorModel Outcome) : Prop :=
  Nonempty model.History ∧ ∀ complete : model.Complete,
    match complete with
    | .terminal _ _ => True
    | .infinite _ _ => False
    | .waiting _ _ => False

def livenessStatement (spec : SpecProcess resources) : LivenessContract → Prop
  | .terminatesUnder assumptions =>
      ∀ interpretation input, spec.admits input →
        if LivenessAssumption.environmentResponsive ∈ assumptions then
          (spec.denotation interpretation input).TerminatesUnderResponsive
        else UnconditionallyTerminates (spec.denotation interpretation input)

def livenessDemand (spec : SpecProcess resources) (fragment : LivenessContract) : AuthoredDemand :=
  ⟨.termination, spec.livenessStatement fragment,
    [⟨"Grass.SpecProcess", "denotation"⟩, ⟨"Grass.SpecProcess", "environmentResponsive"⟩]⟩

def baseRequirements (spec : SpecProcess resources) : DemandFamily :=
  AuthoredDemand.family spec.contract.demands

def authorRows (spec : SpecProcess resources) : List AuthoredDemand :=
  spec.contract.demands ++ spec.liveness.map spec.livenessDemand

/-- Full author theorem suite; compilation consumes its own stage safety laws. -/
def authorRequirements (spec : SpecProcess resources) : DemandFamily :=
  AuthoredDemand.family spec.authorRows

def dependencies (spec : SpecProcess resources) (key : spec.authorRequirements.Key) : List StableId :=
  (spec.authorRows.get (show Fin spec.authorRows.length from key)).dependencies

@[simp] theorem withLiveness_authorRows (spec : SpecProcess resources)
    (fragment : LivenessContract) :
    (spec.withLiveness fragment).authorRows = spec.authorRows ++ [spec.livenessDemand fragment] := by
  simp [authorRows, withLiveness, livenessDemand, livenessStatement, denotation, admits,
    List.map_append, List.append_assoc]

def oldKey (spec : SpecProcess resources) (fragment : LivenessContract)
    (key : spec.authorRequirements.Key) : (spec.withLiveness fragment).authorRequirements.Key :=
  ⟨key.val, by
    change key.val < (spec.withLiveness fragment).authorRows.length
    rw [withLiveness_authorRows, List.length_append]
    have bound : key.val < spec.authorRows.length := key.isLt
    omega⟩

theorem withLiveness_oldIdentity (spec : SpecProcess resources) (fragment : LivenessContract)
    (key : spec.authorRequirements.Key) :
    (spec.withLiveness fragment).authorRequirements.identity (spec.oldKey fragment key) =
      spec.authorRequirements.identity key := rfl

theorem withLiveness_oldStatement (spec : SpecProcess resources) (fragment : LivenessContract)
    (key : spec.authorRequirements.Key) :
    (spec.withLiveness fragment).authorRequirements.statement (spec.oldKey fragment key) =
      spec.authorRequirements.statement key := by
  change ((spec.withLiveness fragment).authorRows[(spec.oldKey fragment key).val]).statement =
    (spec.authorRows[key.val]).statement
  simp only [withLiveness_authorRows, oldKey]
  rw [List.getElem_append_left (show key.val < spec.authorRows.length from key.isLt)]

theorem withLiveness_oldDependencies (spec : SpecProcess resources) (fragment : LivenessContract)
    (key : spec.authorRequirements.Key) :
    (spec.withLiveness fragment).dependencies (spec.oldKey fragment key) =
      spec.dependencies key := by
  change ((spec.withLiveness fragment).authorRows[(spec.oldKey fragment key).val]).dependencies =
    (spec.authorRows[key.val]).dependencies
  simp only [withLiveness_authorRows, oldKey]
  rw [List.getElem_append_left (show key.val < spec.authorRows.length from key.isLt)]

end SpecProcess

/-- Author proof obligations are independent of implementation certificates. -/
def MeetsAllSpecificationTheorems {R : Type} [Resource.ResourceModel R] {resources : R}
    (spec : SpecProcess resources) : Prop :=
  DemandCertificateFamily spec.authorRequirements

end Grass
