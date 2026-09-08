import Grass.Artifact.Binary.Gobj.LinkedTables

/-!
# Structurally validated `.gobj` payloads

`StructurallyValidGobj` retains the exact first-order payload together with the
decoded linked tables and the equality produced by their generic structural
validator. It deliberately carries no certificate or target relocation proof.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Grammar Grass.Std.Logical

/-- A complete payload whose linked generic tables passed structural validation. -/
structure StructurallyValidGobj where
  payload : GobjPayload
  linkedTables : GobjLinkedTables
  linkedExact : parseGobjLinkedTables payload = .ok linkedTables
deriving DecidableEq, Repr

/-- Parse a whole `.gobj` and retain the exact successful structural checks. -/
def parseStructurallyValidGobj (input : Std.Logical.ByteArray) :
    Except ParseError StructurallyValidGobj :=
  match parseGobj input with
  | .error error => .error error
  | .ok payload =>
    match linkedExact : parseGobjLinkedTables payload with
    | .error error => .error error
    | .ok linkedTables => .ok { payload, linkedTables, linkedExact }

/-- Exact component successes determine the complete structural parser result. -/
theorem parseStructurallyValidGobj_of
    {input : Std.Logical.ByteArray} {payload : GobjPayload}
    {linkedTables : GobjLinkedTables}
    (payloadExact : parseGobj input = .ok payload)
    (linkedExact : parseGobjLinkedTables payload = .ok linkedTables) :
    parseStructurallyValidGobj input =
      .ok { payload, linkedTables, linkedExact } := by
  unfold parseStructurallyValidGobj
  rw [payloadExact]
  simp only
  split
  case h_1 error observed =>
    rw [observed] at linkedExact
    contradiction
  case h_2 found observed =>
    have foundEq : found = linkedTables := by
      rw [observed] at linkedExact
      exact Except.ok.inj linkedExact
    subst found
    rfl

/-- Construct canonical bytes and their structurally validated payload witness. -/
def GobjLinkedTables.toStructurallyValid
    (tables : GobjLinkedTables) (payload : GobjPayload)
    (sectionsFit : (writeGobjSectionTable tables.sections).length < 2 ^ 32)
    (symbolsFit : (writeGobjSymbolTable tables.symbols).length < 2 ^ 32)
    (relocationsFit :
      (writeGobjRelocationTable tables.relocations).length < 2 ^ 32) :
    StructurallyValidGobj where
  payload := payload.withLinkedTables tables sectionsFit symbolsFit relocationsFit
  linkedTables := tables
  linkedExact := parseGobjLinkedTables_withLinkedTables payload tables
    sectionsFit symbolsFit relocationsFit

/-- `parseStructurallyValidGobj_write` recovers the exact canonical witness. -/
@[simp] theorem parseStructurallyValidGobj_write
    (tables : GobjLinkedTables) (payload : GobjPayload)
    (sectionsFit : (writeGobjSectionTable tables.sections).length < 2 ^ 32)
    (symbolsFit : (writeGobjSymbolTable tables.symbols).length < 2 ^ 32)
    (relocationsFit :
      (writeGobjRelocationTable tables.relocations).length < 2 ^ 32) :
    parseStructurallyValidGobj
        (writeGobj
          (payload.withLinkedTables tables sectionsFit symbolsFit relocationsFit)) =
      .ok (tables.toStructurallyValid payload sectionsFit symbolsFit
        relocationsFit) := by
  exact parseStructurallyValidGobj_of (parseGobj_write _)
    (parseGobjLinkedTables_withLinkedTables payload tables sectionsFit
      symbolsFit relocationsFit)

/-- Successful structural parsing retains exactly the whole-input payload parse. -/
theorem parseStructurallyValidGobj_payloadExact
    {input : Std.Logical.ByteArray} {parsed : StructurallyValidGobj}
    (success : parseStructurallyValidGobj input = .ok parsed) :
    parseGobj input = .ok parsed.payload := by
  unfold parseStructurallyValidGobj at success
  split at success
  case h_1 => simp_all
  case h_2 payload payloadExact =>
    split at success
    case h_1 => simp_all
    case h_2 linkedTables linkedExact =>
      simp only [Except.ok.injEq] at success
      rw [← success]
      exact payloadExact

end Grass.Artifact.Binary.Gobj
