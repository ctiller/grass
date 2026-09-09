import Grass.Semantics.History

/-! Finite correspondence over initialized, choice-bearing histories. Relations
may use reachability evidence without defining maps on unreachable raw states.
Extension and cut matching are separate obligations. This module does not
establish terminal, infinite, waiting, safety, or whole-program correspondence. -/

namespace Grass.RelationalSystem
universe u v w z

namespace History
variable {Event : Type u} {system : RelationalSystem Event}

def Extension (before after : system.History) : Prop :=
  ∃ state graph, ∃ suffix : system.Path before.state before.graph state graph,
    before.append suffix = after

theorem Extension.refl (history : system.History) : Extension history history := by
  refine ⟨_, _, .nil, ?_⟩
  cases history
  simp [append]

theorem Extension.trans {first middle last : system.History}
    (a : Extension first middle) (b : Extension middle last) : Extension first last := by
  obtain ⟨_, _, pa, rfl⟩ := a
  obtain ⟨_, _, pb, rfl⟩ := b
  refine ⟨_, _, pa.append pb, ?_⟩
  simp only [append]
  congr 1
  exact (Path.append_assoc first.path pa pb).symm

theorem restriction_extension (history : system.History) (count : Nat) :
    Extension (history.restrict count) history :=
  ⟨_, _, (history.path.cut count).after, history.restrict_append count⟩

theorem Extension.choices {before after : system.History} (extension : Extension before after) :
    ∃ suffix, after.path.choices = before.path.choices ++ suffix := by
  obtain ⟨_, _, suffix, rfl⟩ := extension
  exact ⟨suffix.choices, Path.choices_append _ _⟩

end History

/-- Finite, branching-sensitive history correspondence. Complete histories,
outcomes, waits and infinite progress require additional obligations. -/
structure HistoryRelation {A : Type u} {B : Type v} {Observation : Type z}
    (lower : RelationalSystem A) (upper : RelationalSystem B)
    (observeLower : lower.History → Observation)
    (observeUpper : upper.History → Observation) where
  Rel : lower.History → upper.History → Prop
  initialForth : ∀ history, history.path.length = 0 →
    ∃ other, other.path.length = 0 ∧ Rel history other
  initialBack : ∀ history, history.path.length = 0 →
    ∃ other, other.path.length = 0 ∧ Rel other history
  extendForth : ∀ {left right}, Rel left right → ∀ {next},
    History.Extension left next →
    ∃ other, History.Extension right other ∧ Rel next other
  extendBack : ∀ {left right}, Rel left right → ∀ {next},
    History.Extension right next →
    ∃ other, History.Extension left other ∧ Rel other next
  observations : ∀ {left right}, Rel left right → observeLower left = observeUpper right
  cutForth : ∀ {left right}, Rel left right → ∀ count,
    ∃ otherCount, Rel (left.restrict count) (right.restrict otherCount)
  cutBack : ∀ {left right}, Rel left right → ∀ count,
    ∃ otherCount, Rel (left.restrict otherCount) (right.restrict count)

namespace HistoryRelation
variable {A : Type u} {B : Type v} {C : Type w} {Observation : Type z}
variable {lower : RelationalSystem A} {middle : RelationalSystem B}
  {upper : RelationalSystem C}
variable {ol : lower.History → Observation} {om : middle.History → Observation}
  {ou : upper.History → Observation}

def refl (system : RelationalSystem A) (observe : system.History → Observation) :
    HistoryRelation system system observe observe where
  Rel := Eq
  initialForth history empty := ⟨history, empty, rfl⟩
  initialBack history empty := ⟨history, empty, rfl⟩
  extendForth := by intros left right equal next extension; subst right; exact ⟨next, extension, rfl⟩
  extendBack := by intros left right equal next extension; subst right; exact ⟨next, extension, rfl⟩
  observations := congrArg observe
  cutForth := by intros left right equal count; subst right; exact ⟨count, rfl⟩
  cutBack := by intros left right equal count; subst right; exact ⟨count, rfl⟩

def symm (relation : HistoryRelation lower middle ol om) :
    HistoryRelation middle lower om ol where
  Rel left right := relation.Rel right left
  initialForth := relation.initialBack
  initialBack := relation.initialForth
  extendForth := relation.extendBack
  extendBack := relation.extendForth
  observations related := (relation.observations related).symm
  cutForth := relation.cutBack
  cutBack := relation.cutForth

def trans (first : HistoryRelation lower middle ol om)
    (second : HistoryRelation middle upper om ou) : HistoryRelation lower upper ol ou where
  Rel left right := ∃ mid, first.Rel left mid ∧ second.Rel mid right
  initialForth history empty := by
    obtain ⟨mid, hm, firstRel⟩ := first.initialForth history empty
    obtain ⟨last, hl, secondRel⟩ := second.initialForth mid hm
    exact ⟨last, hl, mid, firstRel, secondRel⟩
  initialBack history empty := by
    obtain ⟨mid, hm, secondRel⟩ := second.initialBack history empty
    obtain ⟨start, hs, firstRel⟩ := first.initialBack mid hm
    exact ⟨start, hs, mid, firstRel, secondRel⟩
  extendForth := by
    intro left right related next extension
    obtain ⟨mid, firstRel, secondRel⟩ := related
    obtain ⟨midNext, midExtension, firstNext⟩ := first.extendForth firstRel extension
    obtain ⟨last, lastExtension, secondNext⟩ := second.extendForth secondRel midExtension
    exact ⟨last, lastExtension, midNext, firstNext, secondNext⟩
  extendBack := by
    intro left right related next extension
    obtain ⟨mid, firstRel, secondRel⟩ := related
    obtain ⟨midNext, midExtension, secondNext⟩ := second.extendBack secondRel extension
    obtain ⟨start, startExtension, firstNext⟩ := first.extendBack firstRel midExtension
    exact ⟨start, startExtension, midNext, firstNext, secondNext⟩
  observations := by
    rintro left right ⟨mid, firstRel, secondRel⟩
    exact (first.observations firstRel).trans (second.observations secondRel)
  cutForth := by
    rintro left right ⟨mid, firstRel, secondRel⟩ count
    obtain ⟨midCount, firstCut⟩ := first.cutForth firstRel count
    obtain ⟨lastCount, secondCut⟩ := second.cutForth secondRel midCount
    exact ⟨lastCount, mid.restrict midCount, firstCut, secondCut⟩
  cutBack := by
    rintro left right ⟨mid, firstRel, secondRel⟩ count
    obtain ⟨midCount, secondCut⟩ := second.cutBack secondRel count
    obtain ⟨firstCount, firstCut⟩ := first.cutBack firstRel midCount
    exact ⟨firstCount, mid.restrict midCount, firstCut, secondCut⟩

end HistoryRelation
end Grass.RelationalSystem
