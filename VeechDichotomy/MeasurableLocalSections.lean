module

public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! A surjective local homeomorphism onto a Lindelof space has a genuine
measurable section. Countably many actual local inverse charts cover the
target; the first chart containing a point selects its representative.
No measurable selection or fundamental-domain hypothesis is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.MeasurableLocalSections

open Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [Nonempty X] [LindelofSpace Y]

theorem exists_measurable_rightInverse {f : X → Y} (hf : IsLocalHomeomorph f)
    (hs : Surjective f) : ∃ s : Y → X, Measurable s ∧ RightInverse s f := by
  classical
  let e : X → OpenPartialHomeomorph Y X := hf.localInverseAt
  have hcover : (univ : Set Y) ⊆ ⋃ x : X, (e x).source := by
    intro y _
    obtain ⟨x, rfl⟩ := hs y
    exact mem_iUnion.mpr ⟨x, hf.apply_self_mem_localInverseAt_source⟩
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover
    (fun x : X => (e x).source) (fun x => (e x).open_source) hcover
  let U : ℕ → Set Y := fun n => (e (a n)).source
  let : (n : ℕ) → DecidablePred (U n) := fun _ => Classical.decPred _
  let g : ℕ → Y → X := fun n => (U n).piecewise (e (a n)) (fun _ => Classical.choice ‹Nonempty X›)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    (e (a n)).continuousOn.measurable_piecewise continuousOn_const (e (a n)).open_source.measurableSet
  have hmem : ∀ y : Y, ∃ n : ℕ, y ∈ U n := fun y => mem_iUnion.mp (ha (mem_univ y))
  let s : Y → X := fun y => g (Nat.find (hmem y)) y
  refine ⟨s, Measurable.find hgm (fun n => (e (a n)).open_source.measurableSet) hmem, ?_⟩
  intro y
  have hy : y ∈ U (Nat.find (hmem y)) := Nat.find_spec (hmem y)
  have heq : g (Nat.find (hmem y)) y = e (a (Nat.find (hmem y))) y := by
    simp only [g, piecewise, ite_eq_left hy]
  change f (g (Nat.find (hmem y)) y) = y
  rw [heq]
  exact hf.apply_localInverseAt_of_mem hy

end VeechDichotomy.MeasurableLocalSections
