import Grass.Construct.Source.Close

/-!
# Construction residual reports

Residuals use stable, comparable keys and the normative phase order.  A report
is accepted only when keys are unique, phases are nondecreasing, and the exact
ordered key list equals the reviewed allowlist; proposition text is carried for
proof work but is never used as a comparison surrogate.
-/

namespace Grass.Construct

open Grass.CFG Grass.Construct.Fragment

/-- Ordered construction-checking phases. -/
inductive Phase where
  | elaborate
  | symbolic
  | frame
  | arithmetic
  | ghost
  | close
deriving Repr, DecidableEq

namespace Phase

/-- Numeric rank defining the normative phase order. -/
def rank : Phase → Nat
  | .elaborate => 0
  | .symbolic => 1
  | .frame => 2
  | .arithmetic => 3
  | .ghost => 4
  | .close => 5

/-- Whether the left phase may precede the right phase in a report. -/
def beforeOrEqual (left right : Phase) : Bool := decide (left.rank ≤ right.rank)

end Phase

/-- Stable identity and exact source context of one residual proposition. -/
structure ResidualKey where
  block : Option BlockId
  origin : Option SourceOrigin
  edge : Option ExitTag
  phase : Phase
  subject : StableId
deriving Repr, DecidableEq

/-- One residual proposition paired with its stable review key. -/
structure Residual where
  key : ResidualKey
  proposition : Prop

/-- Staged residual output and the exact reviewed key allowlist selected for it. -/
structure ResidualReport where
  residuals : List Residual
  reviewedAllowlist : List ResidualKey

namespace ResidualReport

/-- Residual keys in report order. -/
def keys (report : ResidualReport) : List ResidualKey :=
  report.residuals.map Residual.key

private def orderedAfter (previous : Phase) : List Phase → Bool
  | [] => true
  | current :: rest => previous.beforeOrEqual current && orderedAfter current rest

/-- Whether residual phases follow the normative nondecreasing phase order. -/
def phasesOrdered (report : ResidualReport) : Bool :=
  match report.keys.map ResidualKey.phase with
  | [] => true
  | first :: rest => orderedAfter first rest

/-- Executable report check with exact, ordered reviewed-key matching. -/
def wellFormed (report : ResidualReport) : Bool :=
  decide report.keys.Nodup &&
  decide report.reviewedAllowlist.Nodup &&
  report.phasesOrdered &&
  decide (report.keys = report.reviewedAllowlist)

/-- Certificate-facing statement for `ResidualReport.wellFormed`. -/
def WellFormed (report : ResidualReport) : Prop := report.wellFormed = true

instance (report : ResidualReport) : Decidable report.WellFormed :=
  inferInstanceAs (Decidable (report.wellFormed = true))

/-- Public decomposition of exact residual-report validity. -/
@[simp] theorem wellFormed_iff (report : ResidualReport) :
    report.WellFormed ↔
      ((report.keys.Nodup ∧ report.reviewedAllowlist.Nodup) ∧
        report.phasesOrdered = true) ∧
      report.keys = report.reviewedAllowlist := by
  simp [WellFormed, wellFormed]

end ResidualReport

end Grass.Construct
