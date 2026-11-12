module

public import VeechDichotomy.CompactRecurrence
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Tactic.Choose

/-! Arbitrarily late compact returns supply an actual strictly
increasing sequence of return times tending to infinity. No continuity
or measure-theoretic recurrence input is required for this extraction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy

open Set Filter Topology

theorem HasCompactReturns.sequence {X : Type*} [TopologicalSpace X] {u : ℝ → X}
    (hu : HasCompactReturns u) :
    ∃ K : Set X, IsCompact K ∧ ∃ t : ℕ → ℝ, StrictMono t ∧ Tendsto t atTop atTop ∧ ∀ n, u (t n) ∈ K := by
  classical
  obtain ⟨K, hK, hreturns⟩ := hu
  choose t hge hmem using fun n : ℕ => (frequently_atTop.mp hreturns) (n : ℝ)
  have ht : Tendsto t atTop atTop := tendsto_atTop_mono hge tendsto_natCast_atTop_atTop
  obtain ⟨σ, hσ, hstrict⟩ := strictMono_subseq_of_tendsto_atTop ht
  exact ⟨K, hK, t ∘ σ, hstrict, ht.comp hσ.tendsto_atTop, fun n => hmem (σ n)⟩

end VeechDichotomy
