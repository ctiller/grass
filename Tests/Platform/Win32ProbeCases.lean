import Grass.Platform.Win32.Console
import Grass.Platform.Win32.WriteFile

/-!
# Semantic cases for future Grass-authored API probes

These cases use the existing API response and publication relations. They do
not emit or execute a program. The first executable consumer is intended to
share Hello World's production PE entry, imports and emitter, with inherited
stdout fixtures supplied by a thin host launcher. That path is an open obligation.
-/
namespace Grass.Tests.Win32ProbeCases

open Grass.Std.Logical
open Grass.Platform.Win32
open Grass.Platform.Win32.WriteFile

def payload : Vec Byte := .fromList [11, 22, 33]
def request : WriteRequest := ⟨123, 3⟩

/-- These semantic cases separate published bytes from the API-visible result.
The failure constructor carries no emitted-byte count. -/
structure Observation where
  response : WriteResponse
  emitted : Nat
  output : Vec Byte

def Conforms (observed : Observation) : Prop :=
  Allowed request observed.response ∧
  Publication payload 0 observed.emitted observed.output ∧
  match observed.response with
  | .success count => observed.emitted = count.toNat
  | .failure _ => True

/-- No independent handwritten acceptance table: each expectation is the result
of deciding the conjunction of the existing semantic relations. -/
instance (observed : Observation) : Decidable (Conforms observed) := by
  let publicationDecidable : Decidable (Publication payload 0 observed.emitted observed.output) :=
    if h : 0 ≤ observed.emitted ∧ observed.emitted ≤ payload.length ∧
        observed.output = (payload.drop 0).take (observed.emitted - 0) then
      .isTrue ⟨h.1, h.2.1, h.2.2⟩
    else .isFalse (fun p => h ⟨p.monotone, p.bounded, p.suffix⟩)
  unfold Conforms
  cases observed.response <;> infer_instance

def observation (response : WriteResponse) (emitted : Nat) : Observation :=
  ⟨response, emitted, payload.take emitted⟩

def successCases : List Observation :=
  [observation (.success 0) 0, observation (.success 1) 1,
   observation (.success 3) 3]

def failureCases : List Observation :=
  [observation (.failure 6) 0, observation (.failure 232) 1,
   observation (.failure 109) 3]

def negativeCases : List Observation :=
  [observation (.success 4) 4,
   observation (.success 2) 1,
   ⟨.success 2, 2, .fromList [22, 11]⟩,
   observation (.failure 6) 4]

theorem successes_admitted : ∀ sample ∈ successCases, Conforms sample := by decide
theorem failure_prefixes_admitted : ∀ sample ∈ failureCases, Conforms sample := by decide
theorem mutations_rejected : ∀ sample ∈ negativeCases, ¬ Conforms sample := by decide

/-- Universally, failure does not justify discarding an already published prefix. -/
theorem failure_allows_every_prefix (code : BitVec 32) (count : Nat)
    (bounded : count ≤ payload.length) : Conforms (observation (.failure code) count) := by
  refine ⟨trivial, ⟨Nat.zero_le _, bounded, ?_⟩, trivial⟩
  simp [observation]

theorem successful_count_matches_publication {sample : Observation} {count : BitVec 32}
    (accepted : Conforms sample) (success : sample.response = .success count) :
    sample.emitted = count.toNat := by
  have same := accepted.2.2
  rw [success] at same
  exact same

end Grass.Tests.Win32ProbeCases
