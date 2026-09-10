import Grass.ISA.Wasm.Target
import Grass.Target.Platform
import Grass.Platform.Hosted.Responds
import Grass.Artifact.Binary.LittleEndian

/-!
# WASI Preview 1 native-call ABI

The Wasm half of the WASI (Preview 1) platform: `decode`s an imported-function
call into `Grass.Platform.Hosted.domain`'s portable requests, `encodeReturn`s
the environment's answer back into the imported function's result values and
linear-memory writes, and supplies `entry`. Authority: the `wasi_snapshot_
preview1` witx interface (`WASI/wasi/phases/snapshot/witx/wasi_snapshot_
preview1.witx` in the `WebAssembly/WASI` repository) for every import's
signature, argument order, and the `errno` enum's numeric values.

Every WASI import name lives in the module namespace `wasi_snapshot_
preview1`; a call through any other module name, or through a field name this
platform does not realize, decodes to `none` (`decode`'s final clause),
leaving the machine stuck -- the correct, visible refusal for a call this
minimal Preview1 subset does not implement (`fd_fdstat_get`,
`fd_prestat_get`, `args_get`, `environ_get`, `path_open`, sockets, ...).

## Decode / encodeReturn table

| Import | Decode | Encode on success | Encode on failure/absence |
|---|---|---|---|
| `fd_write(fd:i32, iovs:i32, iovs_len:i32, nwritten:i32) -> errno:i32` | `fd∈{1,2}`: `Console.write stdout\|stderr bytes`, bytes gathered by reading the `__wasi_ciovec_t` array at `iovs` (`iovs_len` entries, each `(buf_ptr:u32, buf_len:u32)` little-endian) via `NativeCall.read`, then each buffer itself; unreadable iovec/buffer, out-of-range `nwritten` cell, or any other `fd` → `none` | `errno` result `0` (`ESUCCESS`), `nwritten` written as `u32` at the 4th argument | `errno` result `EIO`, no writes |
| `fd_read(fd:i32, iovs:i32, iovs_len:i32, nread:i32) -> errno:i32` | `fd = 0`: `Console.read stdin n` where `n` is the sum of the iovec array's declared buffer lengths; any other `fd`, an unreadable iovec array or buffer, or an out-of-range `nread` cell → `none` | `errno` result `0`, delivered bytes distributed front-to-back across the iovec buffers (each capped at its declared length), `nread` written as `u32` at the 4th argument | `errno` result `EIO`, no writes |
| `proc_exit(rval:i32)` (no return) | `Console.exit rval` (terminal) | n/a: `Console.Response (.exit _) = Empty`, eliminated | n/a |
| `clock_time_get(id:i32, precision:i64, time:i32) -> errno:i32` | `id = 1` (`CLOCK_MONOTONIC`): `Clock.now`; any other clock id, or an out-of-range `time` cell → `none` | `errno` result `0`, nanoseconds written as `u64` at the 3rd argument | (never fails: `Clock.Response` is total) |
| anything else, or any import with an unresolved argument/buffer | unsupported: `none` | — | — |

`fd_write`/`fd_read`'s iovec pointer and `clock_time_get`'s `time` pointer are
re-read from the original `NativeCall.args` inside `encodeReturn`, not
carried in the portable `Request`: `Service.Domain` is address-space-agnostic,
so the linear-memory address an answer gets written to is exactly the kind of
platform/ABI detail the portable vocabulary must not know (mirrors
`Grass.Platform.Linux.Target.X86`'s treatment of `read`/`write`/
`clock_gettime`'s buffer addresses).

## Process entry

WASI's convention is that the loader runs whichever function the module
exports under the name `_start` (`wasi_snapshot_preview1.witx`'s "Linking"
notes; a conforming command module has exactly one such export). `entry`
names it; `Grass.ISA.Wasm.Target.initial` resolves the name through the
module's export section, and an unresolvable name gets stuck on the first
instruction (`Grass.ISA.Wasm.Target.step_initial_of_unresolved`). This
minimal subset realizes no `args_get`/`args_sizes_get`/`environ_get`/
`environ_sizes_get`, so `initialMemory` lays out no argv/envp bytes ahead of
the module's own data segments.
-/

namespace Grass.Platform.WASI.Target

open Grass.ISA.Wasm.Target (NativeCall NativeReturn InitialContext)
open Grass.ISA.Wasm (Value)
open Grass.Service
open Grass.Platform.Hosted (Environment domain)
open Grass.Artifact.Binary (writeU32LE writeU64LE readU32LE)

/-! ## Constants -/

/-- Every WASI Preview1 import lives in this module namespace
(`wasi_snapshot_preview1.witx`'s own name). -/
def wasiModuleName : String := "wasi_snapshot_preview1"

/-- `wasi_snapshot_preview1.witx`, `$clockid`: `monotonic` is the clock id
this platform realizes, matching `Service.Clock`'s domain, which "only ever
promises monotonicity" (`Grass/Platform/Hosted/Clock.lean`). -/
def CLOCK_MONOTONIC : Nat := 1

/-- `wasi_snapshot_preview1.witx`, `$errno` variant `success`, position `0`
in the enum. -/
def ESUCCESS : Nat := 0

/-- `wasi_snapshot_preview1.witx`, `$errno` variant `io` ("I/O error"). Its
enum position (`success` first, the remaining variants alphabetical) is `29`,
not the Linux/POSIX `EIO` value `5`: WASI's `errno` numbering is the witx
enum's own declaration order, unrelated to any OS's `errno.h`. -/
def EIO : Nat := 29

/-- `wasi_snapshot_preview1.witx`, `$errno` variant `nosys` ("function not
supported"), used only for imports/requests this decode never actually
produces (kept so `encodeReturn` is total over the whole hosted `domain`). -/
def ENOSYS : Nat := 52

/-! ## Value helpers -/

/-- The `Nat` an `i32` argument carries; `none` for an `i64` (no WASI Preview1
import in this subset takes one). -/
def i32Nat : Value → Option Nat
  | .i32 bits => some bits.toNat
  | .i64 _ => none

/-- An `errno` result value, per `wasi_snapshot_preview1.witx`'s
`(result $error (expected (error $errno)))` return convention: every import
below returns its `errno` as a single `i32`. -/
def errno (code : Nat) : Value := .i32 (BitVec.ofNat 32 code)

/-- The `Nat` carried by `call.args[index]?`, or `0` if that argument is
absent or not an `i32`. Only ever applied, in `encodeReturn`, to an argument
position `decode` already required to be a present `i32` for this exact
`call` to have produced the request being answered -- the fallback exists
only so this helper is total, not because that case is reachable. -/
def argNat (call : NativeCall) (index : Nat) : Nat :=
  ((call.args[index]?).bind i32Nat).getD 0

/-! ## Iovec helpers

`wasi_snapshot_preview1.witx`'s `$iovec`/`$ciovec`: a `(buf_ptr : u32, buf_len
: u32)` pair, 8 bytes, little-endian. -/

/-- Read one iovec entry at `entryAddr`. -/
def readIovec (call : NativeCall) (entryAddr : Nat) : Option (Nat × Nat) := do
  let hdr ← call.read entryAddr 8
  let (bufPtr, rest) ← readU32LE hdr
  let (bufLen, _) ← readU32LE rest
  some (bufPtr.toNat, bufLen.toNat)

/-- The `(buf_ptr, buf_len)` pairs of the first `count` iovec entries starting
at `iovsPtr`, in order; `none` if any entry is unreadable. -/
def iovecAddrs (call : NativeCall) (iovsPtr : Nat) : Nat → Option (List (Nat × Nat))
  | 0 => some []
  | n + 1 => do
      let rest ← iovecAddrs call iovsPtr n
      let entry ← readIovec call (iovsPtr + n * 8)
      some (rest ++ [entry])

/-- The bytes named by a list of `(buf_ptr, buf_len)` iovec entries,
concatenated front to back; `none` if any buffer is unreadable. -/
def readAllBytes (call : NativeCall) (addrs : List (Nat × Nat)) : Option (List UInt8) :=
  (addrs.mapM (fun p => call.read p.1 p.2)).map List.flatten

/-- Distribute `bytes` across a list of `(buf_ptr, buf_len)` iovec entries,
front to back, capping each entry's write at its own declared length and
stopping once `bytes` is exhausted -- `fd_read`'s "may use fewer than
`iovs_len` buffers" allowance. -/
def distributeIovecs : List (Nat × Nat) → List UInt8 → List (Nat × List UInt8)
  | [], _ => []
  | _, [] => []
  | (bufPtr, bufLen) :: rest, bytes =>
      (bufPtr, bytes.take bufLen) :: distributeIovecs rest (bytes.drop bufLen)

/-! ## Decode -/

/-- Whether the `width`-byte result cell an import promises to write at
`call.args[index]` is inside linear memory. `encodeReturn` is a total
function into `NativeReturn`, which has no failure channel: a write it emits
for an out-of-range address is simply lost. Every import whose answer writes
back through a pointer therefore validates that pointer here, so an
out-of-range one is a refusal (`none`, hence a stuck machine) instead of a
silently discarded write. A real runtime answers `EFAULT`; this platform's
`decode` cannot, because the fault is not a `Console`/`Clock` response — see
the report's `Service.Domain` note. -/
def writableCell (call : NativeCall) (index width : Nat) : Bool :=
  ((call.args[index]?).bind i32Nat).any (fun addr => (call.read addr width).isSome)

/-- Decode one WASI Preview1 import call into `Grass.Platform.Hosted.domain`'s
portable request. See the module docstring's table for the full mapping;
`none` is either a genuine refusal (an unrealized import, an unrecognized
`fd`/clock id, or a malformed argument list) or an unreadable iovec, buffer,
or result cell, all of which the generic machine tier
(`Grass.Target.Machine.stuck_of_undecoded`) turns into a stuck state. -/
def decode (call : NativeCall) : Option domain.Request :=
  if call.moduleName ≠ wasiModuleName then none else
  match call.fieldName, call.args with
  | "fd_write", [fdV, iovsPtrV, iovsLenV, _nwrittenPtrV] =>
      match i32Nat fdV, i32Nat iovsPtrV, i32Nat iovsLenV with
      | some fd, some iovsPtr, some iovsLen =>
          if !writableCell call 3 4 then none else
          match iovecAddrs call iovsPtr iovsLen with
          | none => none
          | some addrs =>
              match readAllBytes call addrs with
              | none => none
              | some bytes =>
                  if fd = 1 then some (.inl (.inl (.write .stdout bytes)))
                  else if fd = 2 then some (.inl (.inl (.write .stderr bytes)))
                  else none
      | _, _, _ => none
  | "fd_read", [fdV, iovsPtrV, iovsLenV, _nreadPtrV] =>
      match i32Nat fdV, i32Nat iovsPtrV, i32Nat iovsLenV with
      | some fd, some iovsPtr, some iovsLen =>
          if fd = 0 then
            if !writableCell call 3 4 then none else
            match iovecAddrs call iovsPtr iovsLen with
            | none => none
            | some addrs =>
                -- The buffers are written by `encodeReturn`, which cannot
                -- fail; reading them here is the bounds check for that write.
                match readAllBytes call addrs with
                | none => none
                | some _ => some (.inl (.inl (.read .stdin (addrs.map Prod.snd).sum)))
          else none
      | _, _, _ => none
  | "proc_exit", [codeV] =>
      match i32Nat codeV with
      | some code => some (.inl (.inl (.exit (UInt32.ofNat code))))
      | none => none
  | "clock_time_get", [idV, _precisionV, _timePtrV] =>
      match i32Nat idV with
      | some clockId =>
          if clockId = CLOCK_MONOTONIC ∧ writableCell call 2 8 = true then some (.inr .now)
          else none
      | none => none
  | _, _ => none

/-! ## encodeReturn -/

/-- Encode the environment's answer as the effect of returning from `call`:
result values pushed on the caller's stack and any linear-memory writes.
Matches on the request before the response, since `domain.Response` is
dependent on it. -/
def encodeReturn (call : NativeCall) : (request : domain.Request) → domain.Response request →
    NativeReturn
  | .inl (.inl (.write _stream _bytes)), response =>
      let nwrittenPtr := argNat call 3
      match response with
      | .accepted n =>
          { results := [errno ESUCCESS], writes := [(nwrittenPtr, writeU32LE (UInt32.ofNat n))] }
      | .failed => { results := [errno EIO], writes := [] }
  | .inl (.inl (.read _stream _max)), response =>
      let iovsPtr := argNat call 1
      let iovsLen := argNat call 2
      let nreadPtr := argNat call 3
      match response with
      | .delivered bytes =>
          let addrs := (iovecAddrs call iovsPtr iovsLen).getD []
          { results := [errno ESUCCESS]
            writes :=
              distributeIovecs addrs bytes ++
                [(nreadPtr, writeU32LE (UInt32.ofNat bytes.length))] }
      | .failed => { results := [errno EIO], writes := [] }
  | .inl (.inl (.query _stream)), _response =>
      -- `decode` never produces this request: this minimal Preview1 subset
      -- does not realize `fd_fdstat_get`/`fd_prestat_get`. Kept only so
      -- `encodeReturn` is total over the whole hosted `domain`.
      { results := [errno ENOSYS], writes := [] }
  | .inl (.inl (.exit _status)), response =>
      -- `Console.Response (.exit _) = Empty`: no answer is ever delivered to
      -- a terminal request, so there is no value to encode.
      response.elim
  | .inl (.inr (.allocate _bytes)), _response =>
      -- `decode` never produces this request: this platform does not
      -- realize the heap domain (no WASI import here grows/allocates linear
      -- memory beyond what a `memory.grow` instruction itself does at the
      -- ISA level). Kept only for `encodeReturn`'s totality.
      { results := [errno ENOSYS], writes := [] }
  | .inl (.inr (.reallocate _handle _bytes)), _response =>
      { results := [errno ENOSYS], writes := [] }
  | .inl (.inr (.release _handle)), _response =>
      { results := [errno ENOSYS], writes := [] }
  | .inr .now, response =>
      let timePtr := argNat call 2
      { results := [errno ESUCCESS], writes := [(timePtr, writeU64LE (UInt64.ofNat response))] }

/-! ## Process entry -/

/-- WASI's entry export name (`wasi_snapshot_preview1.witx`, "Linking"). -/
def startExport : String := "_start"

/-- What the platform hands the machine at entry: the entry export's name,
and no argv/envp bytes (this subset realizes no `args_get`/`environ_get`
family). -/
def entry (_env : Environment) : InitialContext :=
  { startExport := startExport
    initialMemory := [] }

/-- The WASI Preview 1 platform for the Wasm ISA: the first fully wired
platform record of the target seams. -/
def platform : Grass.Target.Platform Grass.ISA.Wasm.isa Grass.Platform.Hosted.domain where
  Environment := Grass.Platform.Hosted.Environment
  Admits := Grass.Platform.Hosted.Admits
  entry := entry
  decode := decode
  Responds := Grass.Platform.Hosted.Responds
  encodeReturn := encodeReturn

end Grass.Platform.WASI.Target
