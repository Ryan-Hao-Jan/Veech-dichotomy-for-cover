module

public import VeechDichotomy.FlowIntegerAverages
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Real-time integral averages differ from their integer-floor
averages by at most 2*C/T for a C-bounded observable. Thus actual
continuous-time statistical profiles follow from integer Koopman
profiles along any diverging real time scale. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FlowAverageFloor

open MeasureTheory Set Filter Topology FlowUnitBlock FlowIntegerAverages

private theorem normalized_bound {A B T n C : ℝ} (hT : 0 < T) (hn : 0 < n) (hnT : n ≤ T)
    (hsmall : T - n ≤ 1) (hC : 0 ≤ C) (hB : |B| ≤ C * n) (hD : |A - B| ≤ C * (T - n)) :
    |A / T - B / n| ≤ 2 * C / T := by
  have hBavg : |B / n| ≤ C := by
    rw [abs_div, abs_of_pos hn]
    exact (div_le_iff₀ hn).mpr hB
  have hid : A / T - B / n = (A - B) / T + (B / n) * (n - T) / T := by
    field_simp [hT.ne', hn.ne']
    ring
  rw [hid]
  calc
    |(A - B) / T + (B / n) * (n - T) / T| ≤ |(A - B) / T| + |(B / n) * (n - T) / T| := by
      simpa only [Real.norm_eq_abs] using norm_add_le ((A - B) / T) ((B / n) * (n - T) / T)
    _ ≤ (C * (T - n)) / T + (C * (T - n)) / T := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hT]
        exact div_le_div_of_nonneg_right hD hT.le
      · rw [abs_div, abs_mul, abs_of_pos hT, abs_of_nonpos (sub_nonpos.mpr hnT), neg_sub]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBavg (sub_nonneg.mpr hnT)) hT.le
    _ = (2 * C * (T - n)) / T := by ring
    _ ≤ 2 * C / T := div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) hsmall) hT.le

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
variable (F : Flow ℝ Ω) (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖g x‖ ≤ C)

include hg hC hbound

theorem bound (x : Ω) {T : ℝ} (hT : 1 ≤ T) :
    |timeAverage F g T x - timeAverage F g (Nat.floor T : ℝ) x| ≤ 2 * C / T := by
  let n : ℝ := (Nat.floor T : ℝ)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hn : 0 < n := by
    change (0 : ℝ) < (Nat.floor T : ℝ)
    exact_mod_cast (Nat.floor_pos.mpr hT)
  have hnT : n ≤ T := Nat.floor_le hTpos.le
  have hsmall : T - n ≤ 1 := by linarith [Nat.lt_floor_add_one T]
  let A := ∫ s in (0 : ℝ)..T, g (F s x)
  let B := ∫ s in (0 : ℝ)..n, g (F s x)
  have hB : |B| ≤ C * n := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := n) (f := fun s => g (F s x)) (C := C) (fun s _ => hbound (F s x))
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hn] using h
  have hD : |A - B| ≤ C * (T - n) := by
    change |(∫ s in (0 : ℝ)..T, g (F s x)) - ∫ s in (0 : ℝ)..n, g (F s x)| ≤ C * (T - n)
    rw [intervalIntegral.integral_interval_sub_left (time_interval_integrable F g hg C hbound x 0 T)
      (time_interval_integrable F g hg C hbound x 0 n)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := n) (b := T) (f := fun s => g (F s x)) (C := C) (fun s _ => hbound (F s x))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hnT)] using h
  simpa only [timeAverage, A, B, n, div_eq_mul_inv, mul_comm] using normalized_bound hTpos hn hnT hsmall hC hB hD

theorem difference_tendsto {I : Type*} {l : Filter I} {T : I → ℝ} (hT : Tendsto T l atTop) (x : Ω) :
    Tendsto (fun i => timeAverage F g (T i) x - timeAverage F g (Nat.floor (T i) : ℝ) x) l (𝓝 0) := by
  have hupper := hT.const_div_atTop (2 * C)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hT.eventually (eventually_ge_atTop (1 : ℝ)), hupper (Iio_mem_nhds hε)] with i hiT hiε
  rw [Real.dist_eq, sub_zero]
  exact (bound F g hg C hC hbound x hiT).trans_lt hiε

theorem tendsto_of_floor {I : Type*} {l : Filter I} {T : I → ℝ} (hT : Tendsto T l atTop) (x : Ω)
    {a : ℝ} (ha : Tendsto (fun i => timeAverage F g (Nat.floor (T i) : ℝ) x) l (𝓝 a)) :
    Tendsto (fun i => timeAverage F g (T i) x) l (𝓝 a) := by
  simpa only [sub_add_cancel, zero_add] using (difference_tendsto F g hg C hC hbound hT x).add ha

end VeechDichotomy.FlowAverageFloor
