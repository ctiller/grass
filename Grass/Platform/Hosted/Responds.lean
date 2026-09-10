import Grass.Platform.Hosted.Console
import Grass.Platform.Hosted.Heap
import Grass.Platform.Hosted.Clock

/-!
# Composing the hosted domain

The full service vocabulary a hosted platform realizes is
`(Console.domain.sum Heap.domain).sum Clock.domain`. `Responds.sum` lifts two
per-domain response relations that share one environment type to a relation
over `Domain.sum`, dispatching on which side of the request the caller made;
it is written generically over any two domains and any shared environment
type, because a hosted platform is not its only client -- any platform that
assembles its service vocabulary from `Domain.sum` needs the same lift.
`Responds` below is the one instance this platform needs: console, heap and
clock, stacked left-associated to match how `domain` itself is built from
`Domain.sum`.

A dependent match on the response (`Response r` depends on `r`) has to know
`r` before it can know what it is matching; `Responds.sum` matches its
`(A.sum B).Request` argument first for exactly that reason, the same
discipline `respondsConsole`, `respondsHeap` and `respondsClock` each follow
for their own request type.
-/

namespace Grass.Platform.Hosted

open Grass.Service

/-- Lift two response relations that share an environment type to a relation
over `Domain.sum A B`, dispatching on which side the request came from. -/
def Responds.sum {Env : Type} {A B : Domain}
    (respondsA : Env → (r : A.Request) → A.Response r → Env → Prop)
    (respondsB : Env → (r : B.Request) → B.Response r → Env → Prop) :
    Env → (r : (A.sum B).Request) → (A.sum B).Response r → Env → Prop
  | env, .inl r, response, env' => respondsA env r response env'
  | env, .inr r, response, env' => respondsB env r response env'

/-- The portable service vocabulary a hosted platform realizes: console I/O,
a heap arena, and a monotonic clock. -/
def domain : Domain := (Console.domain.sum Heap.domain).sum Clock.domain

/-- The environment's side of the full hosted domain. -/
def Responds : Environment → (r : domain.Request) → domain.Response r → Environment → Prop :=
  Responds.sum (Responds.sum respondsConsole respondsHeap) respondsClock

/-- `Responds` only ever appends to the stdout transcript along the console
side of the domain (heap and clock requests cannot touch it at all): it may
leave `stdoutTranscript` alone, but it never rewrites or truncates what is
already there. This is what lets a specification treat `stdoutTranscript` as
an append-only observation of the run so far, safe to compare across two
points in a trace without re-examining everything in between. -/
theorem transcript_prefix_of_responds {env env' : Environment} {r : domain.Request}
    {response : domain.Response r} (h : Responds env r response env') :
    ∃ suffix, env'.stdoutTranscript = env.stdoutTranscript ++ suffix := by
  rcases r with (consoleReq | heapReq) | clockReq
  · exact stdout_prefix h
  · exact ⟨[], by simpa using heap_stdout_unaffected h⟩
  · exact ⟨[], by simpa using clock_stdout_unaffected (r := clockReq) h⟩

end Grass.Platform.Hosted
