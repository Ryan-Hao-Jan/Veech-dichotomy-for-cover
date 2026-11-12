module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.LiminfLimsup

/-! Uniformly positive mass yields a FIXED point returning infinitely
often, even after restriction to any conull set. This is the measure
step needed for fixed generic points in a limiting-rectangle argument;
no ergodic decomposition or independence assumption is used. -/

@[expose] public section

namespace VeechDichotomy.PositiveMassFixedReturns

open MeasureTheory Set Filter
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem mass_limsup (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n)) {δ : ℝ≥0∞}
    (hδ : ∃ᶠ n in atTop, δ ≤ μ (S n)) : δ ≤ μ (limsup S atTop) := by
  let T : ℕ → Set X := fun n => ⋃ m ≥ n, S m
  have hT : Antitone T := by
    intro n m hnm x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    obtain ⟨hmk, hxk⟩ := mem_iUnion.mp hk
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hnm.trans hmk, hxk⟩⟩
  have hTm : ∀ n, NullMeasurableSet (T n) μ :=
    fun _ => (MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => hS _).nullMeasurableSet
  have hbound : ∀ n, δ ≤ μ (T n) := by
    intro n
    obtain ⟨m, hnm, hm⟩ := frequently_atTop.mp hδ n
    exact hm.trans (measure_mono (subset_iUnion_of_subset m (subset_iUnion_of_subset hnm Subset.rfl)))
  rw [limsup_eq_iInf_iSup_of_nat]
  change δ ≤ μ (⋂ n, T n)
  rw [hT.measure_iInter hTm ⟨0, measure_ne_top μ (T 0)⟩]
  exact le_iInf hbound

theorem exists_fixed_return (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    {δ : ℝ≥0∞} (hδpos : 0 < δ) (hδ : ∃ᶠ n in atTop, δ ≤ μ (S n))
    {E : Set X} (hE : μ Eᶜ = 0) : ∃ x ∈ E, ∃ᶠ n in atTop, x ∈ S n := by
  have hpos : 0 < μ (limsup S atTop) := hδpos.trans_le (mass_limsup μ S hS hδ)
  by_contra h
  have hsub : limsup S atTop ⊆ Eᶜ := by
    intro x hx hxE
    exact h ⟨x, hxE, mem_limsup_iff_frequently_mem.mp hx⟩
  exact ne_of_gt hpos (measure_mono_null hsub hE)

end VeechDichotomy.PositiveMassFixedReturns
