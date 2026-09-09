import Grass.Refinement.BehaviorCorrespondence
import Grass.Semantics.BehaviorContract
import Grass.Artifact.Encoding

/-! Relative realization algebra, not the public verified-emission gate.
The selected profile is an explicit parameter. A concrete platform must supply
its fixed execution and mandatory safety definitions before these witnesses
can support public target assurance. Authored theorem demands are not used. -/

namespace Grass

/-- An explicitly relative profile fixes all semantic and obligation functions.
Certificates cannot choose a different execution or safety family per artifact.
This record itself is not evidence that its definitions model a real target. -/
structure RealizationProfile {R : Type} [Resource.ResourceModel R] {resources : R}
    (contract : BehaviorContract resources) where
  Program : Type
  encoding : ArtifactEncoding
  compile : Program → Except String encoding.Artifact
  interpretation : contract.Interpretation
  execution : Std.Logical.ByteArray → contract.Input → BehaviorModel contract.Outcome
  observe : (bytes : Std.Logical.ByteArray) → (input : contract.Input) →
    (execution bytes input).Observation → (contract.denotation interpretation input).Observation
  waits : (bytes : Std.Logical.ByteArray) → (input : contract.Input) →
    WaitTranslation (execution bytes input) (contract.denotation interpretation input)
  safety : Std.Logical.ByteArray → contract.Input → DemandFamily.{0}

/-- The artifact is the result of the selected deterministic construction for
the exact program. All admitted inputs receive loaded entry, safety and full
correspondence evidence; author demands remain outside these fields. -/
structure RealizationCertificate {R : Type} [Resource.ResourceModel R] {resources : R}
    {contract : BehaviorContract resources} (profile : RealizationProfile contract)
    (program : profile.Program) where
  artifact : profile.encoding.Artifact
  compiled : profile.compile program = .ok artifact
  entry : ∀ input, contract.admits input →
    ∃ history : (profile.execution (profile.encoding.write artifact) input).History,
      history.path.length = 0
  safety : ∀ input, contract.admits input →
    DemandCertificateFamily (profile.safety (profile.encoding.write artifact) input)
  correspondence : ∀ input, contract.admits input →
    BehaviorCorrespondence (profile.execution (profile.encoding.write artifact) input)
      (contract.denotation profile.interpretation input)
      (profile.observe (profile.encoding.write artifact) input)
      (profile.waits (profile.encoding.write artifact) input)

namespace RealizationCertificate
variable {R : Type} [Resource.ResourceModel R] {resources : R}
variable {contract : BehaviorContract resources} {profile : RealizationProfile contract}
variable {program : profile.Program}

/-- The relative certificate has only its exact selected artifact's bytes. -/
def bytes (certificate : RealizationCertificate profile program) : Std.Logical.ByteArray :=
  profile.encoding.write certificate.artifact

/-- Parsing these bytes recovers the selected construction's decoded view. -/
theorem decoded_exact (certificate : RealizationCertificate profile program) :
    profile.encoding.read certificate.bytes =
      .done (profile.encoding.decoded certificate.artifact) Std.Logical.Vec.empty :=
  profile.encoding.read_write certificate.artifact

/-- `safety_at` discharges any member of the fixed family's complete key type. -/
theorem safety_at (certificate : RealizationCertificate profile program)
    (input : contract.Input) (admitted : contract.admits input)
    (key : (profile.safety certificate.bytes input).Key) :
    (profile.safety certificate.bytes input).statement key :=
  (certificate.safety input admitted).discharge key

/-- The same deterministic construction cannot certify a different artifact. -/
theorem artifact_unique (first second : RealizationCertificate profile program) :
    first.artifact = second.artifact :=
  Except.ok.inj (first.compiled.symm.trans second.compiled)

theorem bytes_unique (first second : RealizationCertificate profile program) :
    first.bytes = second.bytes :=
  congrArg profile.encoding.write (first.artifact_unique second)

/-- A rejected construction cannot acquire a realization certificate. -/
theorem impossible_of_compile_error (error : String)
    (rejected : profile.compile program = .error error) :
    ¬ Nonempty (RealizationCertificate profile program) := by
  rintro ⟨certificate⟩
  have compiled := certificate.compiled
  rw [rejected] at compiled
  cases compiled

/-- A failing member of the selected artifact's safety family cannot be
avoided by choosing another artifact or another family in the certificate. -/
theorem impossible_of_safety_failure (artifact : profile.encoding.Artifact)
    (compiled : profile.compile program = .ok artifact)
    (input : contract.Input) (admitted : contract.admits input)
    (key : (profile.safety (profile.encoding.write artifact) input).Key)
    (failed : ¬ (profile.safety (profile.encoding.write artifact) input).statement key) :
    ¬ Nonempty (RealizationCertificate profile program) := by
  rintro ⟨certificate⟩
  have same : certificate.artifact = artifact :=
    Except.ok.inj (certificate.compiled.symm.trans compiled)
  have safe := certificate.safety input admitted
  rw [same] at safe
  exact failed (safe.discharge key)

end RealizationCertificate
end Grass
