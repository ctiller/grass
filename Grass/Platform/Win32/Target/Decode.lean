import Grass.Platform.Win32.Target.ImportTable
import Grass.Platform.Win32.Target.Handles
import Grass.Platform.Win32.Target.Domain
import Grass.Platform.Win32.Target.Abi
import Grass.Platform.Hosted.Responds

/-!
# Decoding a Win32 native call into a portable service request

The service vocabulary this platform profile realizes, and `decode`, which
turns a call through a recognized import slot into a request in that
vocabulary. Every case below cites the Win32 API it decodes; see
`Grass/Platform/Win32/Target/Return.lean` for the matching `encodeReturn`
and the module docstring of `Grass/Platform/Win32/Target.lean` for the full
decode table and what is out of scope.

`domain` is built as `Grass.Platform.Hosted.domain.sum Native.domain` rather
than assembled fresh from `Console`/`Heap`/`Clock`, so that this platform's
`Responds` can directly reuse `Grass.Platform.Hosted.Responds`
(`Grass/Platform/Win32/Target.lean`, "Wiring") instead of re-deriving the
environment dynamics `Grass/Platform/Hosted/*.lean` already proves things
about. `Grass.Service.Domain.sum` is not literally associative — `A.sum
(B.sum C)` and `(A.sum B).sum C` are different types, distinguished by where
the `Sum.inl`/`Sum.inr` tags nest — so matching `Hosted.domain`'s own
left-associated shape here, rather than the equally-valid right-associated
one, is what makes the reuse possible at all.
-/

namespace Grass.Platform.Win32.Target

open Grass.Service Grass.ISA.X86.Target

/-- The service vocabulary this platform profile realizes: every request the
shared hosted-process environment already knows how to answer
(`Grass.Platform.Hosted.domain` = console + heap + clock) plus this
profile's own `Native.domain` (`GetProcessHeap`). -/
def domain : Domain := Grass.Platform.Hosted.domain.sum Native.domain

/-- Embed a console request into the composite domain. -/
def consoleRequest (r : Console.Request) : domain.Request := .inl (.inl (.inl r))

/-- Embed a heap request into the composite domain. -/
def heapRequest (r : Heap.Request) : domain.Request := .inl (.inl (.inr r))

/-- Embed a clock request into the composite domain. -/
def clockRequest (r : Clock.Request) : domain.Request := .inl (.inr r)

/-- Embed this profile's own extra request into the composite domain. -/
def nativeRequest (r : Native.Request) : domain.Request := .inr r

/-! ## `GetStdHandle` selectors

Microsoft Learn, "GetStdHandle function",
https://learn.microsoft.com/en-us/windows/console/getstdhandle :
`STD_INPUT_HANDLE = ((DWORD)-10)`, `STD_OUTPUT_HANDLE = ((DWORD)-11)`,
`STD_ERROR_HANDLE = ((DWORD)-12)`, i.e. the low 32 bits of `-10`/`-11`/`-12`
reinterpreted unsigned. -/

def stdInputHandle : UInt32 := 0xFFFFFFF6
def stdOutputHandle : UInt32 := 0xFFFFFFF5
def stdErrorHandle : UInt32 := 0xFFFFFFF4

/-- Decode a Win32 native call into a portable service request, given the
program's own import table.

`none` — leaving the machine stuck, per `Platform.decode`'s contract — for:
a call target this platform never realizes (an unrecognized import, or a
`syscall`-shaped call, which this profile never produces since every request
here is reached through the import table); an `nStdHandle` selector other
than the three standard ones; a `WriteFile`/`ReadFile` handle this platform
never issued (`Handles.streamOf`); an overlapped `WriteFile`/`ReadFile`
(`lpOverlapped ≠ 0`, unsupported in this profile — see
`Grass/Platform/Win32/Target.lean`, "Unsupported"); or a buffer argument that
cannot be read from memory (an out-of-image pointer, a program bug, not a
platform gap). -/
def decode (imports : List Grass.Target.ImportSymbol) (call : NativeCall) :
    Option domain.Request := do
  let .importSlot slotAddress := call.target | none
  let api ← apiOf imports slotAddress
  match api with
  | .getStdHandle =>
      -- BOOL/HANDLE GetStdHandle(DWORD nStdHandle); nStdHandle in RCX.
      let selector := low32 (arg0 call)
      if selector = stdInputHandle then some (consoleRequest (.query .stdin))
      else if selector = stdOutputHandle then some (consoleRequest (.query .stdout))
      else if selector = stdErrorHandle then some (consoleRequest (.query .stderr))
      else none
  | .writeFile =>
      -- BOOL WriteFile(HANDLE hFile, LPCVOID lpBuffer, DWORD nNumberOfBytesToWrite,
      --   LPDWORD lpNumberOfBytesWritten, LPOVERLAPPED lpOverlapped);
      -- hFile, lpBuffer, nNumberOfBytesToWrite, lpNumberOfBytesWritten in
      -- RCX/RDX/R8/R9; lpOverlapped is the first stack argument.
      let lpOverlapped ← stackArgument call 4
      if lpOverlapped = 0 then
        let stream ← Handles.streamOf (arg0 call)
        let bytes ← call.read (arg1 call).toNat (arg2 call).toNat
        some (consoleRequest (.write stream bytes))
      else
        none
  | .readFile =>
      -- BOOL ReadFile(HANDLE hFile, LPVOID lpBuffer, DWORD nNumberOfBytesToRead,
      --   LPDWORD lpNumberOfBytesRead, LPOVERLAPPED lpOverlapped);
      -- same layout as WriteFile. The destination buffer is not read here —
      -- decoding a *read* request needs no input bytes, only where and how
      -- many; `encodeReturn` addresses the buffer again from `call` once the
      -- response delivers the bytes to place there.
      let lpOverlapped ← stackArgument call 4
      if lpOverlapped = 0 then
        let stream ← Handles.streamOf (arg0 call)
        some (consoleRequest (.read stream (arg2 call).toNat))
      else
        none
  | .exitProcess =>
      -- void ExitProcess(UINT uExitCode); uExitCode in RCX.
      some (consoleRequest (.exit (low32 (arg0 call))))
  | .getProcessHeap =>
      -- HANDLE GetProcessHeap(void); no arguments.
      some (nativeRequest .processHeap)
  | .heapAlloc =>
      -- DECLSPEC_ALLOCATOR LPVOID HeapAlloc(HANDLE hHeap, DWORD dwFlags, SIZE_T dwBytes);
      -- hHeap/dwFlags in RCX/RDX are not modeled further: this profile
      -- realizes a single implicit heap (`Heap.domain` carries no heap
      -- identity), so accepting any `hHeap` is an over-approximation, never
      -- a narrowing — docs/PLATFORM_ABI.md's asymmetry rule prefers it.
      some (heapRequest (.allocate (arg2 call).toNat))
  | .heapReAlloc =>
      -- DECLSPEC_ALLOCATOR LPVOID HeapReAlloc(HANDLE hHeap, DWORD dwFlags,
      --   LPVOID lpMem, SIZE_T dwBytes); lpMem/dwBytes in R8/R9.
      some (heapRequest (.reallocate (arg2 call).toNat (arg3 call).toNat))
  | .heapFree =>
      -- BOOL HeapFree(HANDLE hHeap, DWORD dwFlags, LPVOID lpMem); lpMem in R8.
      some (heapRequest (.release (arg2 call).toNat))
  | .queryPerformanceCounter =>
      -- BOOL QueryPerformanceCounter(LARGE_INTEGER *lpPerformanceCount);
      -- the pointer is only needed by `encodeReturn`, to place the counter
      -- value; the request itself carries no argument.
      some (clockRequest .now)

end Grass.Platform.Win32.Target
