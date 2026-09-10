import Tests.ISA.Wasm.Binding

/-! Model validation only. No results from this executable enter proof authority. -/
open Grass.ISA.Wasm

private def localModule : Module :=
  { imports := []
    functions := [⟨⟨[.i32, .i32], [.i32]⟩, [.i32],
      [.localGet 0, .localGet 1, .i32Sub, .localSet 2, .localGet 2]⟩]
    exports := [⟨"run", 0⟩] }

private def constantModule : Module :=
  { imports := []
    functions := [⟨⟨[], [.i64]⟩, [], [.i64Const 0xffffffffffffffff]⟩]
    exports := [⟨"run", 0⟩] }

private def trapModule : Module :=
  { imports := []
    functions := [⟨⟨[], []⟩, [], [.unreachable]⟩]
    exports := [⟨"run", 0⟩] }

def main : IO Unit := do
  IO.FS.createDirAll ".lake/wasm-probe"
  for (name, source) in [("host", Grass.Tests.ISA.Wasm.source),
      ("locals", localModule), ("constant", constantModule), ("trap", trapModule)] do
    match source.encode with
    | none => throw (IO.userError s!"emission refused: {name}")
    | some bytes =>
      IO.FS.writeBinFile s!".lake/wasm-probe/{name}.wasm"
        (ByteArray.mk (bytes.map (fun b => UInt8.ofNat b.toNat)).toArray)
      IO.println s!"emitted {name}: {bytes.length} bytes"
