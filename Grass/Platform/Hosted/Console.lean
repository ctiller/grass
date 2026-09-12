import Grass.Platform.Hosted.Environment

/-!
# Console responses

`respondsConsole` is the environment's side of `Service.Console`: byte
streams and process exit. Every clause matches the request first, so the
response type (`Console.Response` depends on the request) is already pinned
down when the response is matched -- see the module docstring on `Responds`
for why this order is forced.

Partial writes and end-of-stream are not corner cases folded in for
completeness; they are the documented behavior of the hosted I/O APIs this
model has to cover:

* POSIX `write(2)`: "the number of bytes written may be less than nbyte if,
  for example, there is insufficient space on the underlying physical
  medium, or the RLIMIT_FSIZE resource limit is encountered ... or the call
  was interrupted by a signal." A short, successful write is normal, not a
  failure, and is not attributable to the caller doing anything wrong.
* Win32 `WriteFile`: `lpNumberOfBytesWritten` "receives the number of bytes
  written"; MSDN documents that for pipes and other non-seeking devices this
  can be less than `nNumberOfBytesToWrite` while the call still returns
  nonzero (success).
* POSIX `read(2)`: "it is not an error if this number [of bytes read] is
  smaller than the number of bytes requested"; a return of 0 signals
  end-of-file, not failure.

`Console.Request.write`/`.read` are generic over every `Stream`, but this
environment keeps a destination transcript only for stdout/stderr and a
source buffer only for stdin: writing to stdin or reading from stdout/stderr
has nowhere to go, so those combinations can only ever fail here. This is a
modeling choice the `Service.Domain` vocabulary does not itself make (it does
not mark a stream read- or write-only); see the report for this as a
possible vocabulary gap.
-/

namespace Grass.Platform.Hosted

open Grass.Service Grass.Service.Console

/-- The bounds a `write` acceptance count must satisfy: positive and no more
than what was offered, capped by the environment's chunking policy if it has
one. `validAccept` permits `accepted 0` only when nothing was offered, matching the
`bytes = []` case explicitly. -/
def validAccept (bytes : List UInt8) (n : Nat) (chunking : Option Nat) : Prop :=
  (0 < n ∧ n ≤ bytes.length ∧ ∀ cap, chunking = some cap → n ≤ cap) ∨ (n = 0 ∧ bytes = [])

/-- The environment's side of the console domain. -/
def respondsConsole (env : Environment) : (r : Request) → Response r → Environment → Prop
  -- An I/O error is always a possible answer to a write, connected or not.
  | .write _stream _bytes, .failed, env' => env' = env
  | .write .stdout bytes, .accepted n, env' =>
      env.stdoutAvailable = true ∧ validAccept bytes n env.writeChunking ∧
        env' = env.appendStdout (bytes.take n)
  | .write .stderr bytes, .accepted n, env' =>
      env.stderrAvailable = true ∧ validAccept bytes n env.writeChunking ∧
        env' = env.appendStderr (bytes.take n)
  -- stdin has no transcript to accept a write into.
  | .write .stdin _bytes, .accepted _n, _env' => False
  -- An I/O error is always a possible answer to a read, connected or not.
  | .read _stream _max, .failed, env' => env' = env
  | .read .stdin max, .delivered bytes, env' =>
      env.stdinAvailable = true ∧
        ((0 < bytes.length ∧ bytes.length ≤ min max env.stdinRemaining.length ∧
            bytes = env.stdinRemaining.take bytes.length) ∨
          (bytes = [] ∧ env.stdinRemaining = [])) ∧
        env' = env.dropStdin bytes.length
  -- stdout/stderr have no buffered input to deliver.
  | .read .stdout _max, .delivered _bytes, _env' => False
  | .read .stderr _max, .delivered _bytes, _env' => False
  -- Availability is a deterministic, side-effect-free observation.
  | .query stream, isAvailable, env' => isAvailable = env.available stream ∧ env' = env
  -- `Response (.exit s) = Empty`: no response value is ever produced, but
  -- `Machine.Step.terminal` still demands a `Responds` witness to record the
  -- exit event and reach `halted`. `response` is a variable pattern because
  -- `Empty` cannot be matched on constructors; the clause is vacuously total
  -- (no `response` can ever be supplied) and simply says the environment
  -- does not change on the way to halting.
  | .exit _status, _response, env' => env' = env

/-- Failure is never excluded: whatever the stream's state, `.failed` is
always one of the answers `Responds` allows for a `write`. -/
theorem write_failed_always (env : Environment) (s : Stream) (b : List UInt8) :
    respondsConsole env (.write s b) .failed env := rfl

/-- An accepted write never reports more bytes than were offered. -/
theorem write_accepted_le {env env' : Environment} {s : Stream} {b : List UInt8} {n : Nat}
    (h : respondsConsole env (.write s b) (.accepted n) env') : n ≤ b.length := by
  cases s with
  | stdin => exact h.elim
  | stdout =>
      obtain ⟨-, hv, -⟩ := h
      rcases hv with ⟨-, hle, -⟩ | ⟨hz, hb⟩
      · exact hle
      · simp [hz, hb]
  | stderr =>
      obtain ⟨-, hv, -⟩ := h
      rcases hv with ⟨-, hle, -⟩ | ⟨hz, hb⟩
      · exact hle
      · simp [hz, hb]

/-- After an accepted write, the target stream's transcript is exactly the
old transcript with the accepted prefix appended. -/
theorem transcript_append {env env' : Environment} {s : Stream} {b : List UInt8} {n : Nat}
    (h : respondsConsole env (.write s b) (.accepted n) env') :
    (s = .stdout → env'.stdoutTranscript = env.stdoutTranscript ++ b.take n) ∧
      (s = .stderr → env'.stderrTranscript = env.stderrTranscript ++ b.take n) := by
  cases s with
  | stdin => exact h.elim
  | stdout =>
      obtain ⟨-, -, rfl⟩ := h
      refine ⟨fun _ => rfl, fun hs => ?_⟩
      cases hs
  | stderr =>
      obtain ⟨-, -, rfl⟩ := h
      refine ⟨fun hs => ?_, fun _ => rfl⟩
      cases hs

/-- A delivered read is a prefix of the stdin remaining at the time of the
call, and always targets stdin (the only stream this environment can read
from). -/
theorem read_prefix {env env' : Environment} {s : Stream} {max : Nat} {b : List UInt8}
    (h : respondsConsole env (.read s max) (.delivered b) env') :
    s = .stdin ∧ b = env.stdinRemaining.take b.length := by
  cases s with
  | stdin =>
      obtain ⟨-, hb, -⟩ := h
      refine ⟨rfl, ?_⟩
      rcases hb with ⟨-, -, hpre⟩ | ⟨hz, hnil⟩
      · exact hpre
      · simp [hz, hnil]
  | stdout => exact h.elim
  | stderr => exact h.elim

/-- `exit` never changes the environment: the machine records the exit
through the request event itself, not through any effect of `Responds`. -/
theorem exit_preserves {env env' : Environment} {status : UInt32} {response : Empty}
    (h : respondsConsole env (.exit status) response env') : env' = env := h

/-- `respondsConsole` only ever appends to stdout, and only via an accepted
write targeting stdout: every other request and response combination leaves
`stdoutTranscript` exactly as it was. -/
theorem stdout_prefix {env env' : Environment} {r : Request} {response : Response r}
    (h : respondsConsole env r response env') :
    ∃ suffix, env'.stdoutTranscript = env.stdoutTranscript ++ suffix := by
  cases r with
  | write s b =>
      cases response with
      | failed =>
          obtain rfl := h
          exact ⟨[], by simp⟩
      | accepted n =>
          cases s with
          | stdout => obtain ⟨-, -, rfl⟩ := h; exact ⟨b.take n, rfl⟩
          | stderr =>
              obtain ⟨-, -, rfl⟩ := h
              exact ⟨[], by simp [Environment.appendStderr]⟩
          | stdin => exact h.elim
  | read s m =>
      cases response with
      | failed =>
          obtain rfl := h
          exact ⟨[], by simp⟩
      | delivered b =>
          cases s with
          | stdin =>
              obtain ⟨-, -, rfl⟩ := h
              exact ⟨[], by simp [Environment.dropStdin]⟩
          | stdout => exact h.elim
          | stderr => exact h.elim
  | query s =>
      obtain ⟨-, rfl⟩ := h
      exact ⟨[], by simp⟩
  | exit st =>
      obtain rfl := h
      exact ⟨[], by simp⟩

end Grass.Platform.Hosted
