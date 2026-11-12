module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Counts with a uniform additive discrepancy have equal limiting
rates along intervals tending to infinite length. This is a consequence
of the proved finite count bound, not a generic-point/ergodic theorem. -/

@[expose] public section

namespace VeechDichotomy.BoundedCountRates

open Filter Topology

variable {I : Type*} {l : Filter I} {N M : I → ℕ} {T : I → ℝ}

theorem difference_tendsto_zero (C : ℕ) (hT : Tendsto T l atTop)
    (hbound : ∀ᶠ i in l, N i ≤ M i + C ∧ M i ≤ N i + C) :
    Tendsto (fun i => ((N i : ℝ) - (M i : ℝ)) / T i) l (𝓝 0) := by
  have hC : Tendsto (fun i => (C : ℝ) / T i) l (𝓝 0) := hT.const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hT.eventually (eventually_gt_atTop (0 : ℝ)), hbound, hC (Iio_mem_nhds hε)] with i hiT hiB hiC
  have hNM : (N i : ℝ) ≤ (M i : ℝ) + (C : ℝ) := by exact_mod_cast hiB.1
  have hMN : (M i : ℝ) ≤ (N i : ℝ) + (C : ℝ) := by exact_mod_cast hiB.2
  have habs : |(N i : ℝ) - (M i : ℝ)| ≤ (C : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hiT]
  exact (div_le_div_of_nonneg_right habs hiT.le).trans_lt hiC

theorem limits_eq [NeBot l] (C : ℕ) (hT : Tendsto T l atTop)
    (hbound : ∀ᶠ i in l, N i ≤ M i + C ∧ M i ≤ N i + C)
    {a b : ℝ} (hN : Tendsto (fun i => (N i : ℝ) / T i) l (𝓝 a))
    (hM : Tendsto (fun i => (M i : ℝ) / T i) l (𝓝 b)) : a = b := by
  have hdiff : Tendsto (fun i => ((N i : ℝ) - (M i : ℝ)) / T i) l (𝓝 (a - b)) := by
    simpa only [sub_div] using hN.sub hM
  exact sub_eq_zero.mp (tendsto_nhds_unique hdiff (difference_tendsto_zero C hT hbound))

end VeechDichotomy.BoundedCountRates
