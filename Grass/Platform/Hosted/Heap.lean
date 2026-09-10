import Grass.Platform.Hosted.Environment

/-!
# Heap responses

`respondsHeap` is the environment's side of `Service.Heap`: an arena keyed by
opaque handles. Handles are minted from a strictly increasing counter so a
released handle can never alias a later allocation; `heapCapacity` bounds the
arena so allocation failure is always a reachable case, not merely a
theoretical one -- the spikes need to exercise the failure path, and a heap
that can never actually run out cannot exercise it. This matches how a real
allocator is specified: POSIX `malloc` "may fail and return a null pointer"
whenever the implementation cannot satisfy the request, for reasons of its
own it need not disclose (fragmentation, another process's pressure on the
same address space, an administrative limit); the caller is required to
handle failure, not to predict it.
-/

namespace Grass.Platform.Hosted

open Grass.Service Grass.Service.Heap

/-- Two half-open byte ranges `[base, base + size)` share no address. -/
def RangesDisjoint (a b : Nat × Nat) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

/-- The environment's side of the heap domain. -/
def respondsHeap (env : Environment) : (r : Request) → Response r → Environment → Prop
  -- Allocation failure is always a possible answer, whether or not the
  -- request would have fit: a real allocator may refuse for reasons this
  -- model does not track.
  | .allocate _bytes, none, env' => env' = env
  | .allocate bytes, some handle, env' =>
      handle = env.nextHandle ∧ env.liveTotal + bytes ≤ env.heapCapacity ∧
        -- A fresh allocation is fresh: it may not land on any byte already
        -- live in this arena, nor on any byte the loader already claimed for
        -- the program image, stack, or argument block. Picking such an
        -- address is the environment's job (`docs/MEMORY_MODEL.md` §2: every
        -- allocation has a fresh generative identity); a platform whose
        -- `encodeReturn` later treats `handle` as a memory address (see
        -- `Grass.Platform.Linux.Target.X86`) is only ever as sound as this.
        (∀ existing ∈ env.allocations, RangesDisjoint (handle, bytes) existing) ∧
        (∀ region ∈ env.reserved, RangesDisjoint (handle, bytes) region) ∧
        env' = env.pushAllocation handle bytes
  -- Reallocation failure is always possible, and is the only answer to a
  -- dead handle: there is nothing to grow or shrink. On success the arena
  -- may hand back a different handle, as a real allocator's block may move.
  | .reallocate _handle _bytes, none, env' => env' = env
  | .reallocate handle bytes, some handle', env' =>
      env.isLive handle = true ∧ handle' = env.nextHandle ∧
        env.liveTotal - (env.sizeOf? handle).getD 0 + bytes ≤ env.heapCapacity ∧
        env' = (env.removeAllocation handle).pushAllocation handle' bytes
  -- Release is deterministic: it succeeds exactly on a live handle, and the
  -- environment always knows which of the two it is facing.
  | .release handle, true, env' => env.isLive handle = true ∧ env' = env.removeAllocation handle
  | .release handle, false, env' => env.isLive handle = false ∧ env' = env

/-- Allocation failure is never excluded: `none` is always one of the
answers `Responds` allows, whatever the request and whatever the arena's
free space. -/
theorem allocate_failure_always (env : Environment) (bytes : Nat) :
    respondsHeap env (.allocate bytes) none env := rfl

/-- Releasing a live handle can succeed. -/
theorem release_live_true {env : Environment} {handle : Nat} (live : env.isLive handle = true) :
    respondsHeap env (.release handle) true (env.removeAllocation handle) :=
  ⟨live, rfl⟩

/-- Releasing a handle that is not live fails, deterministically. -/
theorem release_dead_false {env : Environment} {handle : Nat} (dead : env.isLive handle = false) :
    respondsHeap env (.release handle) false env :=
  ⟨dead, rfl⟩

/-- `release` never reports success for a dead handle: the two clauses of
`respondsHeap` on `.release` agree with `Environment.isLive` exactly. -/
theorem release_true_iff_live {env env' : Environment} {handle : Nat} :
    respondsHeap env (.release handle) true env' ↔
      env.isLive handle = true ∧ env' = env.removeAllocation handle := Iff.rfl

/-- No heap request ever touches stdout: `respondsHeap` only ever rewrites
`allocations`/`nextHandle`. -/
theorem heap_stdout_unaffected {env env' : Environment} {r : Request} {response : Response r}
    (h : respondsHeap env r response env') : env'.stdoutTranscript = env.stdoutTranscript := by
  cases r with
  | allocate bytes =>
      cases response with
      | none => obtain rfl := h; rfl
      | some handle => obtain ⟨-, -, -, -, rfl⟩ := h; rfl
  | reallocate handle bytes =>
      cases response with
      | none => obtain rfl := h; rfl
      | some handle' => obtain ⟨-, -, -, rfl⟩ := h; rfl
  | release handle =>
      cases response with
      | true => obtain ⟨-, rfl⟩ := h; rfl
      | false => obtain ⟨-, rfl⟩ := h; rfl

end Grass.Platform.Hosted
