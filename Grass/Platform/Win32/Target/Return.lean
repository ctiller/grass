import Grass.Platform.Win32.Target.Decode
import Grass.Artifact.Binary.LittleEndian

/-!
# Encoding a service response as a Win32 call return

`encodeReturn` matches on `request` before `response`
(`domain.Response request` is dependent on `request`; matching them
together as one discriminant pair is the textbook-safe way to eliminate a
dependent scrutinee in Lean 4, and it is what lets the `.exit` arm eliminate
`Empty` outright rather than trying to case on it). Every arm cites the
Win32 API contract it encodes; see
`Grass/Platform/Win32/Target/Decode.lean` for the matching `decode` and
`Grass/Platform/Win32/Target.lean` for the full return table.

Every arm sets `clobbers := Grass.ABI.Win64.volatileRegisters`
(`RAX RCX RDX R8 R9 R10 R11`): a `call`-shaped instruction gives the callee
license to destroy exactly the registers the Win64 convention marks
volatile, no more and no less, whichever API was called.
-/

namespace Grass.Platform.Win32.Target

open Grass.Service Grass.ISA.X86.Target

/-- The clobber set every Win32 API call in this profile shares: the Win64
convention's volatile registers, reused from `Grass.ABI.Win64` rather than
restated. -/
def callClobbers : List Reg := Grass.ABI.Win64.volatileRegisters

/-- A return that only sets `RAX`, with no memory writes — the common case
for a `BOOL`/`HANDLE`/pointer result. -/
def simpleReturn (rax : UInt64) : NativeReturn :=
  { rax := rax, rdx := none, writes := [], clobbers := callClobbers }

/-- A return that sets `RAX` and writes one out-parameter. -/
def writingReturn (rax : UInt64) (write : Nat × List UInt8) : NativeReturn :=
  { rax := rax, rdx := none, writes := [write], clobbers := callClobbers }

/-- A return that sets `RAX` and writes two out-parameters, in order. -/
def writingReturn2 (rax : UInt64) (first second : Nat × List UInt8) : NativeReturn :=
  { rax := rax, rdx := none, writes := [first, second], clobbers := callClobbers }

/-- Encode a service response as the ISA-level effect of returning from a
Win32 API call. -/
def encodeReturn (call : NativeCall) (request : domain.Request) :
    domain.Response request → NativeReturn :=
  match request with
  | .inl (.inl (.inl (.query stream))) =>
      -- HANDLE GetStdHandle(DWORD nStdHandle); response is whether `stream`
      -- is available. On success, RAX is the handle this platform issues
      -- for `stream` (`Handles.value`, recoverable later by `decode`
      -- through `Handles.streamOf`). Microsoft Learn, "GetStdHandle
      -- function": on failure the return value is `INVALID_HANDLE_VALUE`;
      -- this profile answers unavailability with `NULL` (`0`) instead,
      -- since `Console.Request.query`'s `Bool` only distinguishes
      -- available/unavailable and does not distinguish "no such device" —
      -- the documented `NULL` case — from "the handle value itself is
      -- invalid" — the documented `INVALID_HANDLE_VALUE` case, which cannot
      -- arise here since `decode` only ever builds a `.query` request from
      -- one of the three recognized `nStdHandle` selectors.
      fun available =>
        match available with
        | true => simpleReturn (Handles.value stream)
        | false => simpleReturn 0
  | .inl (.inl (.inl (.write ..))) =>
      -- BOOL WriteFile(...); RAX is nonzero on success, zero on failure
      -- (Microsoft Learn, "WriteFile function"). On success, the accepted
      -- byte count is written to `lpNumberOfBytesWritten` (argument 3, R9)
      -- as a little-endian DWORD. On failure, MSDN does not document what
      -- `*lpNumberOfBytesWritten` holds, so nothing is written — the
      -- weaker, permitted claim (docs/PLATFORM_ABI.md's over-approximation
      -- rule: omitting a write the contract does not promise is sound;
      -- inventing one would not be).
      fun response =>
        match response with
        | .accepted count =>
            writingReturn 1 ((arg3 call).toNat, Grass.Artifact.Binary.writeU32LE (UInt32.ofNat count))
        | .failed => simpleReturn 0
  | .inl (.inl (.inl (.read ..))) =>
      -- BOOL ReadFile(...); RAX nonzero on success, zero on failure. On
      -- success, the delivered bytes are written to `lpBuffer` (argument 1,
      -- RDX) and their count to `lpNumberOfBytesRead` (argument 3, R9) as a
      -- little-endian DWORD; the empty list (end of stream) is a
      -- zero-length write and a `0` count, which `WriteFile`'s contract
      -- (docs/HELLO_WORLD.md, zero-byte writes) treats as a legitimate,
      -- allowed outcome rather than a failure, and `ReadFile` is symmetric.
      fun response =>
        match response with
        | .delivered bytes =>
            writingReturn2 1 ((arg1 call).toNat, bytes)
              ((arg3 call).toNat, Grass.Artifact.Binary.writeU32LE (UInt32.ofNat bytes.length))
        | .failed => simpleReturn 0
  | .inl (.inl (.inl (.exit ..))) =>
      -- void ExitProcess(UINT uExitCode); never returns. `Console.Response`
      -- (`Grass/Service/Domain.lean`) makes this precise: `Response (.exit
      -- _) = Empty`, so there is no value to encode a return from — the
      -- type itself says a resumed continuation after `.exit` cannot exist,
      -- eliminated rather than constructed.
      fun response => nomatch response
  | .inl (.inl (.inr (.allocate bytes))) =>
      -- HeapAlloc(...); RAX is the allocated address, or `NULL` on failure
      -- (Microsoft Learn, "HeapAlloc function", heapapi.h: HeapAlloc returns
      -- a pointer to a block of at least `bytes` readable/writable bytes).
      -- On success this answer also maps `[address, address + bytes)`
      -- read/write, non-executable, mirroring Linux `mmap`'s `.allocate`
      -- case (`Grass.Platform.Linux.Target.X86.encodeReturn`) -- without it
      -- the returned pointer would be inaccessible to the machine exactly as
      -- an unmapped `mmap` address would be.
      fun response =>
        match response with
        | some address =>
            { rax := UInt64.ofNat address, rdx := none, writes := [], clobbers := callClobbers
              maps := [{ base := address, size := bytes, readable := true, writable := true }] }
        | none => simpleReturn 0
  | .inl (.inl (.inr (.reallocate handle bytes))) =>
      -- HeapReAlloc(...); RAX is the (possibly relocated) address, or
      -- `NULL` on failure. Whether the original block survives a failed
      -- reallocation is an environment/`Responds` fact, not an
      -- `encodeReturn` one. On success, HeapReAlloc may move the block
      -- (Microsoft Learn, "HeapReAlloc function"): the old region at
      -- `handle` is released (`unmaps`) and a fresh region of `bytes` bytes
      -- is mapped at the (possibly identical) returned `address`.
      fun response =>
        match response with
        | some address =>
            { rax := UInt64.ofNat address, rdx := none, writes := [], clobbers := callClobbers
              unmaps := [handle]
              maps := [{ base := address, size := bytes, readable := true, writable := true }] }
        | none => simpleReturn 0
  | .inl (.inl (.inr (.release handle))) =>
      -- HeapFree(...); RAX/return is nonzero on success, zero on failure. A
      -- successful free removes the block's region (Microsoft Learn,
      -- "HeapFree function"), mirroring Linux `munmap`'s `.release` case.
      fun response =>
        match response with
        | true => { rax := 1, rdx := none, writes := [], clobbers := callClobbers, unmaps := [handle] }
        | false => simpleReturn 0
  | .inl (.inr .now) =>
      -- BOOL QueryPerformanceCounter(LARGE_INTEGER *lpPerformanceCount);
      -- "on systems that run Windows XP or later, this function will
      -- always succeed" (Microsoft Learn, "QueryPerformanceCounter
      -- function"), so RAX is always nonzero here; the counter value is
      -- written to the pointer argument (argument 0, RCX) as a
      -- little-endian 64-bit integer.
      fun counter =>
        writingReturn 1 ((arg0 call).toNat, Grass.Artifact.Binary.writeU64LE (UInt64.ofNat counter))
  | .inr .processHeap =>
      -- GetProcessHeap(); RAX is the default heap's handle, or `NULL` on
      -- failure.
      fun response =>
        match response with
        | some handle => simpleReturn (UInt64.ofNat handle)
        | none => simpleReturn 0

end Grass.Platform.Win32.Target
