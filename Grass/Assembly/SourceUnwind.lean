import Grass.Assembly.SourcePrologue
import Grass.Std.Logical.Vec

namespace Grass.Assembly.SourceUnwind
open Grass.ABI.Win64 Grass.Std.Logical

/-- Typed metadata for the exact derived prologue, in the no-frame-pointer,
no-handler profile. This is structural metadata evidence, not semantic reversal. -/
structure Result (prologue : SourcePrologue.Result) where
  info : UnwindInfo
  checked : UnwindInfo.mk? prologue.unwindLayout ⟨0, 0⟩ .noHandler = some info

def prepare? (prologue : SourcePrologue.Result) : Option (Result prologue) :=
  match checked : UnwindInfo.mk? prologue.unwindLayout ⟨0, 0⟩ .noHandler with
  | none => none
  | some info => some ⟨info, checked⟩

theorem Result.layout_exact {prologue : SourcePrologue.Result} (result : Result prologue) :
    result.info.layout = prologue.unwindLayout :=
  (UnwindInfo.mk?_eq_some result.checked).1

theorem Result.frame_exact {prologue : SourcePrologue.Result} (result : Result prologue) :
    result.info.frame = ⟨0, 0⟩ := (UnwindInfo.mk?_eq_some result.checked).2.1

theorem Result.tail_exact {prologue : SourcePrologue.Result} (result : Result prologue) :
    result.info.tail = .noHandler := (UnwindInfo.mk?_eq_some result.checked).2.2

def Result.bytes {prologue : SourcePrologue.Result} (result : Result prologue) :
    Grass.Std.Logical.ByteArray := Vec.fromList result.info.toBytes

theorem Result.bytes_aligned {prologue : SourcePrologue.Result} (result : Result prologue) :
    result.bytes.length % 4 = 0 := result.info.length_toBytes_aligned

theorem Result.prologue_size {prologue : SourcePrologue.Result} (result : Result prologue) :
    result.info.layout.sizeOfProlog.toNat = (ByteLayout.emitted prologue.generated).length := by
  rw [result.layout_exact]
  exact prologue.stored_prologue_size

theorem Result.instruction_end_offsets {prologue : SourcePrologue.Result}
    (result : Result prologue) :
    result.info.layout.offsets.map BitVec.toNat =
      (List.range prologue.generated.length).map
        (fun index => ByteLayout.offset (ByteLayout.sizes prologue.generated) (index + 1)) := by
  rw [result.layout_exact]
  exact prologue.code_offset_naturals

end Grass.Assembly.SourceUnwind
