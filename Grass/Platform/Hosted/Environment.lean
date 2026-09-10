import Grass.Service.Domain

/-!
# The hosted environment

`Grass.Platform.Hosted.Environment` is the ISA-independent state of the world
outside a hosted program: what it was launched with, what it has said on its
output streams, and the shape of the heap and clock the platform lends it.
Win32, Linux and WASI share this record; only `entry`/`decode`/`encodeReturn`
(the ABI-specific half of `Grass.Target.Platform`) differ per ISA, and are
supplied by a later per-ISA module. `Responds`
(`Grass/Platform/Hosted/Responds.lean`) is the relation that gives these
fields their dynamics.
-/

namespace Grass.Platform.Hosted

open Grass.Service

/-- The world outside a hosted program. Every field is observable: a
specification is a predicate over traces of `Service.Event`, and everything a
trace can ever pin down about the environment is one of these fields (or a
value it produced along the way). Nothing here is a proof artifact or an
implementation detail hidden from the program's own observations. -/
structure Environment where
  /-- The program's argv, fixed for the run. `Responds` never changes it;
  it is here so `Admits`/`entry` (supplied by the per-ISA platform) have
  something to read the program's inputs from. -/
  arguments : List String
  /-- Bytes not yet delivered from stdin. A `read` removes a prefix from the
  front; nothing else shrinks it, and nothing ever grows it -- this
  environment models a stdin whose whole contents were fixed before the
  program started, not one that receives more input while it runs. -/
  stdinRemaining : List UInt8
  /-- Whether stdin is connected at all. A "detached console" (no
  controlling terminal, redirection from `/dev/null` or `NUL`, a closed
  handle) reports `false`; a `query` is deterministic in this flag and a
  `read` against an unavailable stream can only fail. -/
  stdinAvailable : Bool
  /-- Whether stdout is connected. -/
  stdoutAvailable : Bool
  /-- Whether stderr is connected. -/
  stderrAvailable : Bool
  /-- Bytes actually accepted onto stdout so far, in order. This is the only
  thing a specification may ever observe about console output: never the
  program's own buffer or intent, only what the environment has already
  taken (see `Environment.stdoutTranscript` used as an observation, and
  `transcript_prefix_of_responds` in `Responds.lean` for why it is safe to
  treat as append-only). -/
  stdoutTranscript : List UInt8
  /-- Bytes actually accepted onto stderr so far, in order. -/
  stderrTranscript : List UInt8
  /-- The next heap handle this environment will mint. Strictly increasing:
  handles are never reused within one run, so a released handle stays
  recognizably dead (`Environment.isLive` reports `false` forever after)
  instead of silently aliasing a future allocation. -/
  nextHandle : Nat
  /-- The live allocations, as `(handle, size)` pairs. -/
  allocations : List (Nat × Nat)
  /-- The total bytes the arena may have live at once. A platform with an
  effectively unbounded heap can still only admit environments with some
  large finite capacity: without a bound, allocation failure would never be
  a reachable case, and the spikes need to exercise it, not merely permit
  it in principle. -/
  heapCapacity : Nat
  /-- A monotonic clock reading, in the environment's own unit (e.g.
  nanoseconds since an unspecified epoch). `Responds` only ever moves it
  forward. -/
  clock : Nat
  /-- The environment's freedom to accept less than it was offered on a
  single `write`: `some m` caps any one acceptance at `m` bytes (a bounded
  pipe or socket send buffer); `none` means a single write may be accepted
  in full, up to its own length, in one step. This is a property of the
  environment's buffering, stable across many calls, so it is a field here
  rather than a parameter re-chosen at each `write`. -/
  writeChunking : Option Nat

namespace Environment

/-- Whether the named stream is connected. -/
def available (env : Environment) : Stream → Bool
  | .stdin => env.stdinAvailable
  | .stdout => env.stdoutAvailable
  | .stderr => env.stderrAvailable

/-- Append accepted bytes to stdout's transcript. -/
def appendStdout (env : Environment) (bytes : List UInt8) : Environment :=
  { env with stdoutTranscript := env.stdoutTranscript ++ bytes }

/-- Append accepted bytes to stderr's transcript. -/
def appendStderr (env : Environment) (bytes : List UInt8) : Environment :=
  { env with stderrTranscript := env.stderrTranscript ++ bytes }

/-- Drop a delivered prefix from stdin. -/
def dropStdin (env : Environment) (count : Nat) : Environment :=
  { env with stdinRemaining := env.stdinRemaining.drop count }

/-- Whether `handle` currently names a live allocation. -/
def isLive (env : Environment) (handle : Nat) : Bool :=
  env.allocations.any (fun a => a.1 == handle)

/-- The size of `handle`'s live allocation, if any. -/
def sizeOf? (env : Environment) (handle : Nat) : Option Nat :=
  (env.allocations.find? (fun a => a.1 == handle)).map Prod.snd

/-- Total bytes currently live in the arena. -/
def liveTotal (env : Environment) : Nat :=
  env.allocations.foldl (fun total a => total + a.2) 0

/-- Record a fresh allocation and advance the handle counter. -/
def pushAllocation (env : Environment) (handle bytes : Nat) : Environment :=
  { env with
    allocations := (handle, bytes) :: env.allocations
    nextHandle := env.nextHandle + 1 }

/-- Drop one allocation from the live set. -/
def removeAllocation (env : Environment) (handle : Nat) : Environment :=
  { env with allocations := env.allocations.filter (fun a => a.1 != handle) }

end Environment

/-- The environments this platform is willing to start a program in: an
unavailable stdin has nothing buffered (there is no upstream process that
could have written to a stream that was never connected), the arena starts
empty under a positive capacity, and no output has been produced before the
program's first instruction runs. -/
def Admits (env : Environment) : Prop :=
  (env.stdinAvailable = false → env.stdinRemaining = []) ∧
  env.allocations = [] ∧
  0 < env.heapCapacity ∧
  env.stdoutTranscript = [] ∧
  env.stderrTranscript = []

end Grass.Platform.Hosted
