import Grass.Unsafe.Emit

namespace Grass.Tests.Unsafe.Emit

open Grass Grass.Std.Logical Grass.Unsafe Grass.Unsafe.Emit

private def first : Construct.Bytes :=
  Construct.bytes [0x90] .encodingShape [.semantics]

private def second : Construct.Bytes :=
  Construct.bytes [0xCC, 0xC3] .controlTargets [.citations]

private def hierarchy : Hierarchy :=
  .group [.leaf (.ofRaw first), .group [], .group [.leaf (.ofRaw second)]]

private def recordingWriter : Writer (List ByteSeq) Unit where
  write seen bytes := .ok (seen ++ [bytes])

example : hierarchy.inputs = [[0x90], [0xCC, 0xC3]] := by native_decide
example : hierarchy.taints =
    [⟨.encodingShape, [.semantics]⟩, ⟨.controlTargets, [.citations]⟩] := by
  native_decide

example : emit recordingWriter [] hierarchy = .ok
    { state := [[0x90], [0xCC, 0xC3]]
      inputs := [[0x90], [0xCC, 0xC3]]
      taints :=
        [⟨.encodingShape, [.semantics]⟩, ⟨.controlTargets, [.citations]⟩] } := by
  simp [emit, run, hierarchy, Hierarchy.inputs, Hierarchy.taints, Chunk.ofRaw,
    first, second, recordingWriter]

private inductive Failure where
  | refused
deriving Repr, DecidableEq

private def refusingWriter : Writer Nat Failure where
  write count bytes := if bytes = [0xCC, 0xC3] then .error .refused else .ok (count + 1)

example : emit refusingWriter 0 hierarchy = .error .refused := by
  simp [emit, run, hierarchy, Hierarchy.inputs, Chunk.ofRaw, first, second,
    refusingWriter]

example {receipt : Receipt (List ByteSeq)}
    (h : emit recordingWriter [] hierarchy = .ok receipt) :
    receipt.state = [[0x90], [0xCC, 0xC3]] := by
  have exactCalls := emit_state h
  have computed : run recordingWriter [] hierarchy.inputs =
      .ok [[0x90], [0xCC, 0xC3]] := by
    simp [run, hierarchy, Hierarchy.inputs, Chunk.ofRaw, first, second,
      recordingWriter]
  rw [computed] at exactCalls
  exact Except.ok.inj exactCalls |>.symm

example {receipt : Receipt (List ByteSeq)}
    (h : emit recordingWriter [] hierarchy = .ok receipt) :
    receipt.inputs = hierarchy.inputs := emit_inputs h

example {receipt : Receipt (List ByteSeq)}
    (h : emit recordingWriter [] hierarchy = .ok receipt) :
    receipt.taints = hierarchy.taints := emit_taints h

end Grass.Tests.Unsafe.Emit
