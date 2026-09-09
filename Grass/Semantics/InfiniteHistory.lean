import Grass.Semantics.History

/-! Finite, choice-bearing prefixes of an existing infinite
continuation. No transition data is reconstructed or selected. -/
namespace Grass.RelationalSystem.InfiniteContinuation

universe u
variable {Event : Type u} {system : RelationalSystem Event}
variable {state : system.State} {graph : system.Graph} {priorEvents : List Event}

private def castStart {s₀ s finish : system.State} {g₀ g fg : system.Graph}
    (hs : s₀ = s) (hg : g₀ = g) (path : system.Path s₀ g₀ finish fg) :
    system.Path s g finish fg := by subst s; subst g; exact path

private theorem castStart_events {s₀ s finish : system.State} {g₀ g fg : system.Graph}
    (hs : s₀ = s) (hg : g₀ = g) (path : system.Path s₀ g₀ finish fg) :
    (castStart hs hg path).events = path.events := by subst s; subst g; rfl
private theorem castStart_choices {s₀ s finish : system.State} {g₀ g fg : system.Graph}
    (hs : s₀ = s) (hg : g₀ = g) (path : system.Path s₀ g₀ finish fg) :
    (castStart hs hg path).choices = path.choices := by subst s; subst g; rfl
private theorem castStart_length {s₀ s finish : system.State} {g₀ g fg : system.Graph}
    (hs : s₀ = s) (hg : g₀ = g) (path : system.Path s₀ g₀ finish fg) :
    (castStart hs hg path).length = path.length := by subst s; subst g; rfl

private theorem castStart_snoc {s₀ s finish next : system.State}
    {g₀ g fg nextGraph : system.Graph} (hs : s₀ = s) (hg : g₀ = g)
    (path : system.Path s₀ g₀ finish fg) (choice : system.Choice) (event : Event)
    (valid : system.Step fg finish choice event next nextGraph) :
    castStart hs hg (path.snoc choice event next nextGraph valid) =
      (castStart hs hg path).snoc choice event next nextGraph valid := by
  subst s; subst g; rfl

private def rawPrefix (continuation : system.InfiniteContinuation state graph priorEvents) :
    (length : Nat) → system.Path (continuation.stateAt 0) (continuation.graphAt 0)
      (continuation.stateAt length) (continuation.graphAt length)
  | 0 => .nil
  | length + 1 => .snoc (rawPrefix continuation length) (continuation.choiceAt length)
      (continuation.eventAt length) (continuation.stateAt (length + 1))
      (continuation.graphAt (length + 1)) (continuation.step length)

private theorem rawPrefix_events (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : (rawPrefix continuation length).events = continuation.prefixEvents length := by
  induction length with
  | zero => rfl
  | succ length ih => simp [rawPrefix, Path.events, InfiniteContinuation.prefixEvents, ih]
private theorem rawPrefix_choices (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : (rawPrefix continuation length).choices =
      (List.range length).map continuation.choiceAt := by
  induction length with
  | zero => rfl
  | succ length ih => simp [rawPrefix, Path.choices, ih, List.range_succ, List.map_append]
private theorem rawPrefix_length (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : (rawPrefix continuation length).length = length := by
  induction length with
  | zero => rfl
  | succ length ih => simp [rawPrefix, Path.length, ih]

/-- Retain the first `length` actual transitions from the declared frontier. -/
def prefixPath (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : system.Path state graph
      (continuation.stateAt length) (continuation.graphAt length) :=
  castStart continuation.stateZero continuation.graphZero (rawPrefix continuation length)

/-- `prefixPath_succ` appends the actual next choice and transition to the same path. -/
theorem prefixPath_succ (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : continuation.prefixPath (length + 1) =
      (continuation.prefixPath length).snoc (continuation.choiceAt length)
        (continuation.eventAt length) (continuation.stateAt (length + 1))
        (continuation.graphAt (length + 1)) (continuation.step length) := by
  exact castStart_snoc continuation.stateZero continuation.graphZero
    (rawPrefix continuation length) (continuation.choiceAt length)
    (continuation.eventAt length) (continuation.step length)

/-- The retained path contains exactly the existing continuation event prefix. -/
theorem prefixPath_events (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : (prefixPath continuation length).events = continuation.prefixEvents length := by
  rw [prefixPath, castStart_events, rawPrefix_events]

/-- Every actual indexed choice is retained in order. -/
theorem prefixPath_choices (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : (prefixPath continuation length).choices =
      (List.range length).map continuation.choiceAt := by
  rw [prefixPath, castStart_choices, rawPrefix_choices]

/-- The path has one transition for each requested continuation index. -/
theorem prefixPath_length (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) : (prefixPath continuation length).length = length := by
  rw [prefixPath, castStart_length, rawPrefix_length]

/-- Erasing the retained choices yields the existing finite-prefix witness. -/
theorem prefixPath_steps (continuation : system.InfiniteContinuation state graph priorEvents)
    (length : Nat) :
    (prefixPath_events continuation length) ▸
      (prefixPath continuation length).steps = continuation.prefixSteps length := by
  apply Subsingleton.elim

end Grass.RelationalSystem.InfiniteContinuation
