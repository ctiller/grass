import Grass.Refinement.Realization
import Tests.Refinement.ImplementationConformance

/-! The relative gate accepts the shared success-only implementation fixture
without demanding the abstract error alternative. Artifact rejection and
admitted-input entry coverage remain independent obligations. -/

namespace Grass.Tests.Refinement.Realization

open Grass.Tests.Refinement.ImplementationConformance

variable {R : Type} [Resource.ResourceModel R]

def language : BehaviorLanguage R (inferInstance : Resource.ResourceModel R) where
  Syntax := ULift Unit
  Snapshot := fun _ => Unit
  Input := fun _ => Unit
  Outcome := fun _ => Bool
  Interpretation := fun _ => Unit
  admits := fun _ _ => True
  denotation := fun _ _ _ _ _ => successOrError
  demands := fun _ _ _ => []

def contract (resources : R) : BehaviorContract resources :=
  ⟨language, ⟨()⟩, ()⟩

def encoding : ArtifactEncoding where
  Artifact := Unit
  Parsed := Unit
  write := fun _ => Std.Logical.Vec.empty
  read := fun bytes => .done () bytes
  decoded := fun _ => ()
  read_write := fun _ => rfl

def noSafety : DemandFamily where
  Key := Empty
  keys := []
  complete key := nomatch key
  unique := by simp
  identity key := nomatch key
  identityInjective key := nomatch key
  kind key := nomatch key
  statement key := nomatch key

def profile (resources : R) : RealizationProfile (contract resources) where
  Program := Bool
  encoding := encoding
  compile accepted := if accepted then .ok () else .error "rejected"
  interpretation := ()
  execution := fun _ _ => successOnly
  observe := fun _ _ => id
  waits := fun _ _ => successTranslation
  safety := fun _ _ => noSafety

/-- The actual directed fixture constructs the complete relative certificate;
the upper error branch is not a required implementation result. -/
def certificate (resources : R) : RealizationCertificate (profile resources) true where
  artifact := ()
  compiled := rfl
  entry := fun _ _ => ⟨successOnlyInitial, rfl⟩
  safety := fun _ _ => ⟨fun key => nomatch key⟩
  correspondence := fun _ _ => successConformance

theorem rejected_program_has_no_certificate (resources : R) :
    ¬ Nonempty (RealizationCertificate (profile resources) false) :=
  RealizationCertificate.impossible_of_compile_error "rejected" rfl

/-- No chosen artifact or conformance witness can hide a missing initial
history at an admitted input. This does not require termination. -/
theorem missing_entry_prevents_certificate
    {resources : R} {selected : RealizationProfile (contract resources)}
    {program : selected.Program}
    (missing : ∀ artifact, selected.compile program = .ok artifact →
      ¬ ∃ history : (selected.execution (selected.encoding.write artifact) ()).History,
        history.path.length = 0) :
    ¬ Nonempty (RealizationCertificate selected program) := by
  rintro ⟨cert⟩
  exact missing cert.artifact cert.compiled (cert.entry () trivial)

end Grass.Tests.Refinement.Realization
