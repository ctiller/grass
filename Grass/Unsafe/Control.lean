import Grass.Unsafe.Raw

/-!
# Imported control-flow evidence

`ControlEvidence.wellFormed` checks imported direct targets against an admitted
finite set and requires one nonempty, duplicate-free selection for every unique
indirect site.  It does not promote raw instructions to a verified fragment;
`ClosedImport` only packages the checked structural evidence for a later
Construct-layer proof.
-/

namespace Grass.Unsafe

universe u v w

/-- One control-flow demand projected from an imported instruction. -/
inductive ControlDemand (Target : Type v) (Site : Type w) where
  | direct (target : Target)
  | indirect (site : Site)
deriving Repr, DecidableEq

/-- Consumer-supplied exact control-demand projection. -/
structure ControlModel (Instruction : Type u) (Target : Type v) (Site : Type w) where
  project : Instruction → List (ControlDemand Target Site)

/-- One projected control demand at its exact flattened instruction index. -/
structure LocatedControlDemand (Target : Type v) (Site : Type w) where
  instructionIndex : Nat
  demand : ControlDemand Target Site
deriving Repr, DecidableEq

/-- Selected finite target family for one imported indirect-control site. -/
structure IndirectSelection (Target : Type v) (Site : Type w) where
  site : Site
  targets : List Target
deriving Repr, DecidableEq

namespace RawHierarchy

variable {Instruction : Type u} {Target : Type v} {Site : Type w}

private def locateControlFrom (model : ControlModel Instruction Target Site) :
    Nat → List Instruction → List (LocatedControlDemand Target Site)
  | _, [] => []
  | instructionIndex, instruction :: rest =>
      (model.project instruction).map (fun demand => ⟨instructionIndex, demand⟩) ++
        locateControlFrom model (instructionIndex + 1) rest

/-- Exact control demands from the flattened raw instruction list. -/
def controlDemands (raw : RawHierarchy Instruction)
    (model : ControlModel Instruction Target Site) :
    List (LocatedControlDemand Target Site) :=
  locateControlFrom model 0 raw.flatten

end RawHierarchy

/-- Finite control-target evidence selected for one exact raw hierarchy. -/
structure ControlEvidence {Instruction : Type u} {Target : Type v} {Site : Type w}
    (raw : RawHierarchy Instruction) (model : ControlModel Instruction Target Site) where
  admittedTargets : List Target
  indirect : List (IndirectSelection Target Site)

namespace ControlEvidence

variable {Instruction : Type u} {Target : Type v} {Site : Type w}
  {raw : RawHierarchy Instruction} {model : ControlModel Instruction Target Site}
  [DecidableEq Target] [DecidableEq Site]

/-- Indirect site identities in flattened instruction and projection order. -/
def demandedIndirectSites (_evidence : ControlEvidence raw model) : List Site :=
  (raw.controlDemands model).filterMap fun located =>
    match located.demand with
    | .direct _ => none
    | .indirect site => some site

/-- Selected indirect site identities in evidence order. -/
def selectedIndirectSites (evidence : ControlEvidence raw model) : List Site :=
  evidence.indirect.map IndirectSelection.site

/-- Imported direct demands whose target is not admitted. -/
def unresolvedDirect (evidence : ControlEvidence raw model) :
    List (LocatedControlDemand Target Site) :=
  (raw.controlDemands model).filter fun located =>
    match located.demand with
    | .direct target => decide (target ∉ evidence.admittedTargets)
    | .indirect _ => false

/-- Whether every indirect selection is nonempty, duplicate-free, and confined
to the admitted target set. -/
def indirectSelectionsValid (evidence : ControlEvidence raw model) : Bool :=
  evidence.indirect.all fun selection =>
    decide (selection.targets ≠ []) &&
    decide selection.targets.Nodup &&
    selection.targets.all fun target => evidence.admittedTargets.contains target

/-- Executable closure check for imported control-flow evidence. -/
def wellFormed (evidence : ControlEvidence raw model) : Bool :=
  decide evidence.admittedTargets.Nodup &&
  decide evidence.demandedIndirectSites.Nodup &&
  decide (evidence.selectedIndirectSites = evidence.demandedIndirectSites) &&
  evidence.unresolvedDirect.isEmpty &&
  evidence.indirectSelectionsValid

/-- Certificate-facing statement for `ControlEvidence.wellFormed`. -/
def WellFormed (evidence : ControlEvidence raw model) : Prop :=
  evidence.wellFormed = true

instance (evidence : ControlEvidence raw model) : Decidable evidence.WellFormed :=
  inferInstanceAs (Decidable (evidence.wellFormed = true))

/-- Closed evidence has no unresolved imported direct target. -/
theorem unresolvedDirect_eq_nil (evidence : ControlEvidence raw model)
    (closed : evidence.WellFormed) : evidence.unresolvedDirect = [] := by
  simp [WellFormed, wellFormed] at closed
  exact closed.1.2

end ControlEvidence

/-- Raw imported hierarchy paired with checked control-target evidence. -/
structure ClosedImport {Instruction : Type u} {Target : Type v} {Site : Type w}
    (model : ControlModel Instruction Target Site) [DecidableEq Target]
    [DecidableEq Site] where
  raw : RawHierarchy Instruction
  evidence : ControlEvidence raw model
  closed : evidence.WellFormed

/-- Structured reason control-target evidence could not be closed. -/
inductive ControlEvidenceError (Target : Type v) (Site : Type w) where
  | duplicateAdmittedTargets (targets : List Target)
  | duplicateDemandedSites (sites : List Site)
  | indirectSitesMismatch (selected demanded : List Site)
  | unresolvedDirect (demands : List (LocatedControlDemand Target Site))
  | invalidIndirectSelections (selections : List (IndirectSelection Target Site))
deriving Repr, DecidableEq

namespace ControlEvidence

variable {Instruction : Type u} {Target : Type v} {Site : Type w}
  {raw : RawHierarchy Instruction} {model : ControlModel Instruction Target Site}
  [DecidableEq Target] [DecidableEq Site]

/-- Check raw control evidence totally, returning either a closed package or the
first structural failure in checker order. -/
def close (evidence : ControlEvidence raw model) :
    Except (ControlEvidenceError Target Site) (ClosedImport model) :=
  if admittedUnique : evidence.admittedTargets.Nodup then
    if sitesUnique : evidence.demandedIndirectSites.Nodup then
      if sitesExact : evidence.selectedIndirectSites = evidence.demandedIndirectSites then
        if directClosed : evidence.unresolvedDirect = [] then
          if indirectClosed : evidence.indirectSelectionsValid = true then
            .ok {
              raw := raw
              evidence := evidence
              closed := by
                simp [WellFormed, wellFormed, admittedUnique, sitesUnique,
                  sitesExact, directClosed, indirectClosed]
            }
          else
            .error (.invalidIndirectSelections evidence.indirect)
        else
          .error (.unresolvedDirect evidence.unresolvedDirect)
      else
        .error (.indirectSitesMismatch evidence.selectedIndirectSites
          evidence.demandedIndirectSites)
    else
      .error (.duplicateDemandedSites evidence.demandedIndirectSites)
  else
    .error (.duplicateAdmittedTargets evidence.admittedTargets)

end ControlEvidence

end Grass.Unsafe
