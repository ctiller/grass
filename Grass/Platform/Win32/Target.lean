import Grass.Platform.Win32.Target.ImportTable
import Grass.Platform.Win32.Target.Handles
import Grass.Platform.Win32.Target.Domain
import Grass.Platform.Win32.Target.Abi
import Grass.Platform.Win32.Target.Decode
import Grass.Platform.Win32.Target.Return
import Grass.Platform.Win32.Target.Entry

/-!
# The Win32 (x86-64) platform

The Win32 instance of `Grass.Target.Platform` (`Grass/Target/Platform.lean`):
which `KERNEL32.dll` import means which API
(`Grass/Platform/Win32/Target/ImportTable.lean`), the Win64 ABI's argument
placement (`Grass/Platform/Win32/Target/Abi.lean`), the fixed standard-handle
values (`Grass/Platform/Win32/Target/Handles.lean`), `decode`
(`Grass/Platform/Win32/Target/Decode.lean`), `encodeReturn`
(`Grass/Platform/Win32/Target/Return.lean`) and `entry`
(`Grass/Platform/Win32/Target/Entry.lean`). `Admits` and `Responds` below
reuse `Grass.Platform.Hosted` (`Grass/Platform/Hosted/*.lean`) in full.

None of the 70 legacy `Grass/Platform/Win32/*.lean` files (`ApiDispatch.lean`,
`WriteFile*.lean`, `RawStep.lean`, ...) are imported or modified here: they
model a program-shaped `WriteFile` machine tier `docs/TARGET_SEAMS.md` retires,
and this module owes them nothing.

## Decode table

| Win32 API | Request |
|---|---|
| `GetStdHandle(STD_INPUT_HANDLE)` | `Console.Request.query .stdin` |
| `GetStdHandle(STD_OUTPUT_HANDLE)` | `Console.Request.query .stdout` |
| `GetStdHandle(STD_ERROR_HANDLE)` | `Console.Request.query .stderr` |
| `GetStdHandle(other)` | none (stuck) |
| `WriteFile(hFile, buf, n, _, lpOverlapped = 0)` | `Console.Request.write stream bytes`, `stream` from `Handles.streamOf hFile`, `bytes` from `call.read buf n` |
| `WriteFile(..., lpOverlapped ≠ 0)` | none (stuck — overlapped I/O unsupported) |
| `ReadFile(hFile, _, n, _, lpOverlapped = 0)` | `Console.Request.read stream n` |
| `ExitProcess(code)` | `Console.Request.exit code` (terminal) |
| `HeapAlloc(_, _, bytes)` | `Heap.Request.allocate bytes` |
| `HeapReAlloc(_, _, mem, bytes)` | `Heap.Request.reallocate mem bytes` |
| `HeapFree(_, _, mem)` | `Heap.Request.release mem` |
| `GetProcessHeap()` | `Native.Request.processHeap` |
| `QueryPerformanceCounter(_)` | `Clock.Request.now` |
| unrecognized import / `syscall` call | none (stuck) |

## `encodeReturn` table

| Request | Response | `RAX` | Memory writes |
|---|---|---|---|
| `query stream` | `true`/`false` | `Handles.value stream` / `0` | — |
| `write ..` | `.accepted n` | `1` | `lpNumberOfBytesWritten ← n` (`DWORD`) |
| `write ..` | `.failed` | `0` | — |
| `read ..` | `.delivered bs` | `1` | `lpBuffer ← bs`; `lpNumberOfBytesRead ← bs.length` (`DWORD`) |
| `read ..` | `.failed` | `0` | — |
| `exit ..` | (`Empty`) | eliminated (`nomatch`); never actually invoked — see "Terminal requests" below | — |
| `allocate ..` | `some a` / `none` | `a` / `0` | — |
| `reallocate ..` | `some a` / `none` | `a` / `0` | — |
| `release ..` | `true`/`false` | `1`/`0` | — |
| `Clock.now` | `counter` | `1` | `lpPerformanceCount ← counter` (8 bytes) |
| `processHeap` | `some h` / `none` | `h` / `0` | — |

Every return's `clobbers` is `Grass.ABI.Win64.volatileRegisters`
(`RAX RCX RDX R8 R9 R10 R11`).

## Unsupported

- **Overlapped I/O.** `WriteFile`/`ReadFile` decode only when
  `lpOverlapped = 0`; a nonzero `lpOverlapped` decodes to `none`, which is
  stuck rather than silently synchronous. A profile that wants overlapped
  I/O needs its own request shape in `Console`/an extra domain, which this
  platform does not add.
- **`GetLastError`.** No request or response here carries an error code, so
  a program that calls `GetLastError` after a failure reads an import this
  platform does not recognize (`apiOf` returns `none` for it, since it is
  not a constructor of `Api`) and gets stuck. Modeling it needs either
  environment-carried error state or a response variant that names the
  reason, neither of which the cited MSDN contracts for `WriteFile` et al.
  require this profile to promise.
- **`GetCommandLineW` / the argument block.** `entry`'s `argumentBlock` is
  always empty; a program that parses its own command line decodes an
  unrecognized import and gets stuck the same way.
- **`CreateFile` and any handle beyond the three standard streams.**
  `Handles` only knows `stdin`/`stdout`/`stderr`; there is no way to open a
  new file in this profile.

## Terminal requests (`ExitProcess`)

`Grass.Service.Console.Response` (`Grass/Service/Domain.lean`) sets
`Response (.exit _) = Empty`: there is no value to encode a return from,
which `encodeReturn`'s `.exit` arm reflects by eliminating `response`
(`fun response => nomatch response`) rather than constructing one. This
module observed, while it was being written, that `Grass/Target/Machine.lean`
did not yet have a transition that could ever reach `.halted` from an
`.exit` call under that `Empty` response type — its `Step.terminal` rule
required a concrete `response : D.Response request`, which no `.exit` call
could ever supply. That gap has since been closed upstream (a concurrent
change to `Grass/Target/Machine.lean`, outside this platform's scope, per
`docs/TARGET_SEAMS.md` rule 1): `Step.call` now additionally requires
`¬ D.Terminal request`, and a new `Step.exit` rule transitions a terminal
call straight from `running` to `halted` without ever consulting `decode`'s
platform-supplied `encodeReturn` or the environment's `Responds` at all. So
`encodeReturn`'s `.exit` arm here, while still required by
`Grass.Target.Platform.encodeReturn`'s totality obligation over
`D.Response request`, is now provably unreachable at run time — `Empty`
elimination is exactly the right implementation of a function the machine
never calls.

## Wiring

`Admits`/`Responds` reuse `Grass.Platform.Hosted` (`Grass/Platform/Hosted/*.lean`,
authored concurrently with this module and now present in this tree) for
every request this platform shares with Linux/WASI, and add only this
profile's own `Native.responds` for `GetProcessHeap`. `domain`
(`Grass/Platform/Win32/Target/Decode.lean`) is built as
`Grass.Platform.Hosted.domain.sum Native.domain` — matching
`Hosted.domain`'s own left-associated `Domain.sum` nesting exactly, rather
than the equally valid but incompatible right-associated shape — precisely
so this reuse typechecks.
-/

namespace Grass.Platform.Win32.Target

open Grass.Service

/-- The environments this platform is willing to start a program in. This
profile adds no restriction of its own beyond the shared hosted-process
ones. -/
def Admits : Grass.Platform.Hosted.Environment → Prop := Grass.Platform.Hosted.Admits

/-- The environment's side of the full request vocabulary this platform
realizes: the shared hosted dynamics for console/heap/clock
(`Grass.Platform.Hosted.Responds`), lifted alongside this profile's own
`Native.responds` for `GetProcessHeap` by `Responds.sum`
(`Grass/Platform/Hosted/Responds.lean`) — the same generic lift
`Grass.Platform.Hosted.Responds` itself is built from, reused rather than
re-derived. -/
def Responds : Grass.Platform.Hosted.Environment → (r : domain.Request) →
    domain.Response r → Grass.Platform.Hosted.Environment → Prop :=
  Grass.Platform.Hosted.Responds.sum Grass.Platform.Hosted.Responds Native.responds

end Grass.Platform.Win32.Target

/-!
## Dependency not yet available: `Grass.ISA.X86.isa`

The x86 ISA record (`Instr`, `encode`/`decode`, `State`, `step`) does not
exist yet in this tree — only `Grass/ISA/X86/Target/Native.lean`
(`NativeCall`, `NativeReturn`, `InitialContext`, `Fault`) and
`Grass/ISA/X86/Target/Encode.lean` are present, and this module is built
entirely against those. `decode`/`encodeReturn`/`entry` above already have
exactly the shapes `Grass.Target.Platform` needs
(`NativeCall → Option D.Request`,
`NativeCall → (r : D.Request) → D.Response r → NativeReturn`,
`Environment → InitialContext`), and `Admits`/`Responds` above are complete,
so once `Grass.ISA.X86.isa` lands (assigning `isa.NativeCall`,
`isa.NativeReturn` and `isa.InitialContext` to exactly the types
`Native.lean` already declares, as that file's own module docstring
anticipates), the only new code this platform needs is pure wiring:

```
def platform (imports : List Grass.Target.ImportSymbol)
    (config : StackConfig Environment) :
    Grass.Target.Platform Grass.ISA.X86.isa domain :=
  { Environment := Environment
    Admits := Admits
    entry := entry config
    decode := decode imports
    Responds := Responds
    encodeReturn := encodeReturn }
```

`StackConfig` (`Grass/Platform/Win32/Target/Entry.lean`) stays parameterized
even after `isa` lands: `Grass.Platform.Hosted.Environment` (now available)
carries no stack-placement fields at all — a per-run loader decision, not a
portable "world outside the program" fact a specification could observe —
so `entry`'s stack configuration is supplied by whoever assembles `platform`
for a concrete run, not baked into `Environment` itself.

## Build

`lake build Grass.Platform.Win32.Target` (this file) also builds every
helper above, since each is imported transitively. No `sorry`, `axiom`,
`native_decide`, `unsafe`, `implemented_by` or `extern` appears anywhere in
this directory; `warningAsError` is on for the whole build.
-/
