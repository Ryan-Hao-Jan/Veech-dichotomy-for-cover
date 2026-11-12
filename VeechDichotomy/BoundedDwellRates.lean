module

public import VeechDichotomy.BoundedCountRates
public import Mathlib.Tactic.FieldSimp

/-! A bounded dwell-time discrepancy converts an actual occupation
limit into a crossing-rate limit. The interval lengths may vary and
only have to tend to infinity. -/

@[expose] public section

namespace VeechDichotomy.BoundedDwellRates

open Filter Topology

variable {I : Type*} {l : Filter I} {N : I → ℕ} {D L : I → ℝ}

theorem error_tendsto_zero (h C : ℝ) (hL : Tendsto L l atTop)
    (hbound : ∀ᶠ i in l, |D i - h * (N i : ℝ)| ≤ C) :
    Tendsto (fun i => (D i - h * (N i : ℝ)) / L i) l (𝓝 0) := by
  have hC : Tendsto (fun i => C / L i) l (𝓝 0) := hL.const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ)), hbound,
    hC (Iio_mem_nhds hε)] with i hiL hiB hiC
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hiL]
  exact (div_le_div_of_nonneg_right hiB hiL.le).trans_lt hiC

theorem crossing_rate {h m : ℝ} (hh : h ≠ 0) (C : ℝ) (hL : Tendsto L l atTop)
    (hbound : ∀ᶠ i in l, |D i - h * (N i : ℝ)| ≤ C)
    (havg : Tendsto (fun i => D i / L i) l (𝓝 m)) :
    Tendsto (fun i => (N i : ℝ) / L i) l (𝓝 (m / h)) := by
  have herror := error_tendsto_zero h C hL hbound
  have hscaled : Tendsto (fun i => h * (N i : ℝ) / L i) l (𝓝 m) := by
    convert havg.sub herror using 1
    · funext i
      rw [sub_div]
      ring
    · simp
  convert hscaled.div_const h using 1
  funext i
  field_simp [hh]

end VeechDichotomy.BoundedDwellRates
