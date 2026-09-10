import Grass.Refinement.FiniteHistoryRelation

/-! Directed conformance of actual initialized histories. Cuts retain the
prefixes of a matched history; they do not require unchosen upper alternatives. -/

namespace Grass.RelationalSystem
universe u v z

structure HistorySimulation {A : Type u} {B : Type v} {Observation : Type z}
    (lower : RelationalSystem A) (upper : RelationalSystem B)
    (observeLower : lower.History → Observation)
    (observeUpper : upper.History → Observation) where
  Rel : lower.History → upper.History → Prop
  initialForth : ∀ history, history.path.length = 0 →
    ∃ other, other.path.length = 0 ∧ Rel history other
  extendForth : ∀ {left right}, Rel left right → ∀ {next},
    History.Extension left next →
    ∃ other, History.Extension right other ∧ Rel next other
  observations : ∀ {left right}, Rel left right → observeLower left = observeUpper right
  cutForth : ∀ {left right}, Rel left right → ∀ count,
    ∃ otherCount, Rel (left.restrict count) (right.restrict otherCount)
  cutBack : ∀ {left right}, Rel left right → ∀ count,
    ∃ otherCount, Rel (left.restrict otherCount) (right.restrict count)

namespace HistorySimulation

/-- Exact history correspondence supplies directed conformance without changing
its relation, observations, or retained prefix witnesses. -/
def ofExact {A : Type u} {B : Type v} {Observation : Type z}
    {lower : RelationalSystem A} {upper : RelationalSystem B}
    {observeLower : lower.History → Observation}
    {observeUpper : upper.History → Observation}
    (exact : HistoryRelation lower upper observeLower observeUpper) :
    HistorySimulation lower upper observeLower observeUpper where
  Rel := exact.Rel
  initialForth := exact.initialForth
  extendForth := exact.extendForth
  observations := exact.observations
  cutForth := exact.cutForth
  cutBack := exact.cutBack

end HistorySimulation
end Grass.RelationalSystem
