import Grass.ISA.X86.Execution.DecodedSite

/-! Linear byte evidence using the production x64 decoder. The dependent chain
retains every input byte, including a refused suffix. It is not a CFG, a fetch
receipt, an execution trace, or a memory-safety certificate. -/
namespace Grass.Disasm

open Grass.Std.Logical Grass.ISA.X86 Grass.ISA.X86.Execution

/-- Resource exhaustion is distinct from refusal by the selected ISA profile. -/
inductive StopReason where
  | decode (error : DecodedSite.Error)
  | budget
deriving DecidableEq, Repr

/-- Every next site consumes exactly the preceding decoder's suffix at its
nonwrapping linear cursor. Branch semantics do not affect this listing cursor. -/
inductive Linear : BitVec 64 → ByteSeq → Type where
  | done (pc : BitVec 64) : Linear pc []
  | stopped {pc : BitVec 64} {bytes : ByteSeq} (reason : StopReason) : Linear pc bytes
  | next {pc : BitVec 64} {bytes : ByteSeq} (site : DecodedSite pc bytes)
      (tail : Linear site.fallthroughRip site.rest) : Linear pc bytes

/-- Bounded evidence production never skips an unsupported byte to resume later. -/
def scan : Nat → (pc : BitVec 64) → (bytes : ByteSeq) → Linear pc bytes
  | _, pc, [] => .done pc
  | 0, _, _ :: _ => .stopped .budget
  | fuel + 1, pc, byte :: bytes =>
      match DecodedSite.check pc (byte :: bytes) with
      | .error error => .stopped (.decode error)
      | .ok site => .next site (scan fuel site.fallthroughRip site.rest)

namespace Linear

/-- Diagnostic projection of a decoded row; exact bytes remain in its encoding. -/
structure Row where
  pc : BitVec 64
  encoding : InsnEncoding

def rows {pc : BitVec 64} {bytes : ByteSeq} : Linear pc bytes → List Row
  | .done _ => []
  | .stopped _ => []
  | .next site tail => ⟨pc, site.encoding⟩ :: tail.rows

def consumed {pc : BitVec 64} {bytes : ByteSeq} : Linear pc bytes → ByteSeq
  | .done _ => []
  | .stopped _ => []
  | .next site tail => site.encoding.toBytes ++ tail.consumed

def remaining {pc : BitVec 64} {bytes : ByteSeq} : Linear pc bytes → ByteSeq
  | .done _ => []
  | .stopped _ => bytes
  | .next _ tail => tail.remaining

def stop {pc : BitVec 64} {bytes : ByteSeq} : Linear pc bytes → Option StopReason
  | .done _ => none
  | .stopped reason => some reason
  | .next _ tail => tail.stop

/-- A listing partitions the original input exactly; neither skipped bytes nor
invented instruction bytes can disappear behind its presentation. -/
theorem partition {pc : BitVec 64} {bytes : ByteSeq} (listing : Linear pc bytes) :
    listing.consumed ++ listing.remaining = bytes := by
  induction listing with
  | done => rfl
  | stopped => rfl
  | next site tail ih =>
      simp only [consumed, remaining, List.append_assoc, ih]
      exact site.bytesExact.symm

/-- The displayed rows contain precisely the consumed instruction bytes. -/
theorem rows_bytes {pc : BitVec 64} {bytes : ByteSeq} (listing : Linear pc bytes) :
    (listing.rows.flatMap fun row => row.encoding.toBytes) = listing.consumed := by
  induction listing with
  | done => rfl
  | stopped => rfl
  | next site tail ih => simp [rows, consumed, ih]

end Linear
end Grass.Disasm
