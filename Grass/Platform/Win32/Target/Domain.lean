import Grass.Service.Domain
import Grass.Platform.Hosted.Environment

/-!
# Win32-specific service requests

Requests this platform realizes that are not part of the portable
`Grass.Service` vocabulary, because they name something specific to the
Win32 heap API rather than a fact meaningful the same way on Linux or WASI:
`GetProcessHeap` returns a handle to the process's one default heap, a
query with no argument that a *portable* vocabulary would have no shared way
to express (Linux/WASI programs do not ask a platform for "the" heap handle
at all; they allocate directly). Composed into the full request vocabulary
via `Domain.sum` in `Grass/Platform/Win32/Target/Decode.lean`, alongside the
portable `Console`, `Heap` and `Clock` families, the same way every other
platform-specific extra would be.
-/

namespace Grass.Platform.Win32.Target.Native

open Grass.Service

/-- Requests this profile realizes outside the portable domains. -/
inductive Request where
  /-- `GetProcessHeap()`: the handle to the process's default heap. -/
  | processHeap
deriving DecidableEq, Repr

/-- `GetProcessHeap` can fail (Microsoft Learn, "GetProcessHeap function",
https://learn.microsoft.com/en-us/windows/win32/api/heapapi/nf-heapapi-getprocessheap :
"If the function fails, the return value is NULL"), so the response is
optional, the same shape as `Heap.Request.allocate`'s. -/
def Response : Request → Type
  | .processHeap => Option Nat

/-- No request in this small extra domain ends the program. -/
def domain : Domain where
  Request := Request
  Response := Response
  Terminal := fun _ => False

/-- The fixed handle this profile's `GetProcessHeap` always answers with.
Nothing about its concrete value is observable beyond consistency with
itself: `HeapAlloc`/`HeapReAlloc`/`HeapFree` do not check the `hHeap`
argument they are handed against it (`Grass/Platform/Win32/Target/Decode.lean`,
"heapAlloc"), since `Grass.Service.Heap` carries no heap identity at all —
this platform realizes exactly one heap, and any distinct value would serve
equally well. -/
def heapHandle : Nat := 1

/-- `GetProcessHeap` deterministically succeeds with `heapHandle`, leaving
the environment unchanged. Microsoft Learn documents that it *can* fail
("If the function fails, the return value is NULL"), but only under
conditions — exhausted OS resources — `Grass.Platform.Hosted.Environment`
has no field to represent, so the only response this profile allows is the
successful one; nothing here claims the real API can never fail, only that
this environment model has no notion of the failure it would report. -/
def responds (env : Grass.Platform.Hosted.Environment) :
    (r : Request) → Response r → Grass.Platform.Hosted.Environment → Prop
  | .processHeap, response, env' => response = some heapHandle ∧ env' = env

end Grass.Platform.Win32.Target.Native
