import Grass.ISA.Wasm.LocalStep

namespace Grass.Tests.ISA.Wasm
open Grass.ISA.Wasm

/-- Validation fixture only: emitted by the same producer used by Artifact.

`Tools/WasmProbe.lean` emits this module's bytes to `.lake/wasm-probe/host.wasm`
and `tools/wasm-probe.cjs` instantiates and runs them under Node's real
`WebAssembly` engine, checking the host-call arguments/result and the trap
behaviour of the other emitted modules. That is the external ground truth this
fixture exists to feed; it is the reason this module survives while the rest
of this file's former internal `LocalRun`/`HostInvocation`/`localStep`
unit checks (proof-shaped facts about pure functions, not real-world
comparisons) were removed. -/
def source : Module :=
  { imports := [⟨"env", "observe", ⟨[.i32, .i32], [.i32]⟩⟩]
    functions := [⟨⟨[], [.i32]⟩, [],
      [.i32Const 7, .i32Const 3, .i32Sub, .i32Const 5, .call 0]⟩]
    exports := [⟨"run", 1⟩] }

end Grass.Tests.ISA.Wasm
