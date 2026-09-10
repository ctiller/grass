import Grass.Platform.Hosted.Environment

/-!
# Clock responses

`respondsClock` is the environment's side of `Service.Clock`: a single
monotonic reading. The environment may report any value at or after its
current reading, and that value becomes the new current reading -- the one
law a "steady" hosted clock needs. POSIX documents `CLOCK_MONOTONIC` as
representing "monotonic time since some unspecified starting point" that
"shall not be affected by discontinuous jumps"; Win32's
`QueryPerformanceCounter`/`GetTickCount64` and WASI's `monotonic` clock are
specified the same way. Wall-clock time (which can jump backward on
correction) is deliberately not this domain: `Service.Clock` only ever
promises monotonicity.
-/

namespace Grass.Platform.Hosted

open Grass.Service Grass.Service.Clock

/-- The environment's side of the clock domain. -/
def respondsClock (env : Environment) : (r : Request) → Response r → Environment → Prop
  | .now, t, env' => env.clock ≤ t ∧ env' = { env with clock := t }

/-- The clock never runs backward: every answer to `now` is at least the
prior reading, and becomes the new one. -/
theorem clock_monotone {env env' : Environment} {t : Nat}
    (h : respondsClock env .now t env') : env.clock ≤ env'.clock := by
  obtain ⟨hle, rfl⟩ := h
  exact hle

/-- No clock request ever touches stdout: `respondsClock` only ever
rewrites `clock`. -/
theorem clock_stdout_unaffected {env env' : Environment} {r : Request} {response : Response r}
    (h : respondsClock env r response env') : env'.stdoutTranscript = env.stdoutTranscript := by
  cases r with
  | now => obtain ⟨-, rfl⟩ := h; rfl

end Grass.Platform.Hosted
