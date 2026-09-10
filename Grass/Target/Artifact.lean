import Grass.Target.Machine
import Grass.Target.Raw

/-!
# The artifact seam

A `Format` is a writer, a reader, the round-trip law, and the assembled
program an artifact carries. The generic construction `toArtifactFormat`
turns any format into the certificate's `ArtifactFormat spec` by defining the
loaded behavior of a byte string as: read it with the format's reader, and run
the generic machine on the program it carries. `loadExact` then follows from
`read_write` alone, so PE, ELF, Wasm modules and flat boot images share one
proof and supply only their reader/writer pair.

`Parses bytes a` means `bytes` is the canonical serialization of `a`. This is
the exact-emission identity the certificate needs: the bytes `emitProgram`
returns are the bytes whose loaded behavior was certified, not merely bytes
that some reader accepts.
-/

namespace Grass.Target

open Grass.Service

/-- A container format over assembled programs of type `Raw`. -/
structure Format (Raw : Type) where
  /-- The container model: headers, layout, and the carried program. -/
  Artifact : Type
  /-- Build a container for a program, refusing ill-formed input. -/
  assemble : Raw → Option Artifact
  /-- The canonical bytes of a container. -/
  write : Artifact → List UInt8
  /-- Recover a container from bytes. -/
  read : List UInt8 → Option Artifact
  /-- The reader inverts the writer. -/
  read_write : ∀ artifact, read (write artifact) = some artifact
  /-- The program a container carries. -/
  rawOf : Artifact → Raw
  /-- Assembling preserves the program exactly. -/
  rawOf_assemble : ∀ raw artifact, assemble raw = some artifact → rawOf artifact = raw

/-- Lean's packed byte array from a list. -/
def bytesOfList (bytes : List UInt8) : ByteArray := ⟨⟨bytes⟩⟩

/-- The list of a packed byte array, by the underlying array projection so the
round trip with `bytesOfList` is definitional. -/
def listOfBytes (bytes : ByteArray) : List UInt8 := bytes.data.toList

@[simp] theorem listOfBytes_bytesOfList (bytes : List UInt8) :
    listOfBytes (bytesOfList bytes) = bytes := rfl

/-- The behavior of bytes no reader accepts: no initial state. It has no
executions, so it can never be certified. -/
def unloadable (spec : SpecRoot) : ProgramBehavior spec where
  system :=
    { State := spec.Input
      Choice := Unit
      Graph := Unit
      Initial := fun _ _ => False
      Step := fun _ _ _ _ _ _ => False
      Terminal := fun _ _ => False
      InfiniteConsistent := fun _ _ _ _ _ => True
      Extends := fun _ _ => True
      extendsRefl := fun _ => trivial
      extendsTrans := fun _ _ => trivial
      stepExtends := fun _ => trivial }
  inputOf := id

variable {isa : ISA} {D : Domain}

/-- The certificate's artifact format for a container format, an ISA, and a
platform: loaded behavior is the generic machine on the carried program. -/
def toArtifactFormat (format : Format isa.Raw) (platform : Platform isa D)
    (spec : SpecRoot) (eventOf : Event D → spec.AuditEvent)
    (inputOf : platform.Environment → spec.Input) : ArtifactFormat spec where
  Artifact := format.Artifact
  write artifact := bytesOfList (format.write artifact)
  Parses bytes artifact := bytes = bytesOfList (format.write artifact)
  writeParses _ := rfl
  parseExact parses := parses
  artifactBehavior artifact :=
    Machine.behavior platform (format.rawOf artifact) spec eventOf inputOf
  loadedBehavior bytes :=
    match format.read (listOfBytes bytes) with
    | some artifact => Machine.behavior platform (format.rawOf artifact) spec eventOf inputOf
    | none => unloadable spec
  loadExact := by
    intro bytes artifact parses
    subst parses
    simp only [listOfBytes_bytesOfList, format.read_write]

end Grass.Target
