module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-! One strictly increasing subsequence yields almost-everywhere limits
for COUNTABLY many convergence-in-measure problems, allowing a different
measure in each row. A proved diagonal small-error selection and the
first Borel-Cantelli lemma discharge the simultaneous extraction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CountableConvergenceInMeasure

open MeasureTheory Filter Set Topology Finset
open scoped ENNReal

private def tolerance (n : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ n

private theorem tolerance_pos (n : ℕ) : 0 < tolerance n := by
  unfold tolerance
  exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) n

theorem simultaneous {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    (μ : ℕ → Measure Ω) (F : ℕ → ℕ → Ω → E) (G : ℕ → Ω → E)
    (hF : ∀ j, TendstoInMeasure (μ j) (F j) atTop (G j)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, ∀ᵐ x ∂μ j,
      Tendsto (fun k => F j (σ k) x) atTop (𝓝 (G j x)) := by
  have hsmall : ∀ k, ∀ᶠ n in atTop, ∀ j ∈ range (k + 1),
      μ j {x | tolerance k ≤ edist (F j n x) (G j x)} ≤ tolerance k := by
    intro k
    apply (eventually_all_finset (range (k + 1))).mpr
    intro j _
    have he : ∀ᶠ n : ℕ in atTop, μ j {x | tolerance k ≤ edist (F j n x) (G j x)} < tolerance k :=
      (hF j (tolerance k) (tolerance_pos k)) (Iio_mem_nhds (tolerance_pos k))
    exact he.mono (fun _ hn => hn.le)
  choose N hN using (fun k => eventually_atTop.mp (hsmall k))
  let σ : ℕ → ℕ := Nat.rec (N 0) (fun k a => max (a + 1) (N (k + 1)))
  have hσs : ∀ k, σ (k + 1) = max (σ k + 1) (N (k + 1)) := fun _ => rfl
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ (fun k =>
    (Nat.lt_succ_self (σ k)).trans_le (by rw [hσs]; exact le_max_left _ _))
  have hNσ : ∀ k, N k ≤ σ k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => rw [hσs]; exact le_max_right _ _
  refine ⟨σ, hσ, ?_⟩
  intro j
  let bad : ℕ → Set Ω := fun k => if j ≤ k then {x | tolerance k ≤ edist (F j (σ k) x) (G j x)} else ∅
  have hbad : ∀ k, μ j (bad k) ≤ tolerance k := by
    intro k
    by_cases hjk : j ≤ k
    · change μ j (if j ≤ k then {x | tolerance k ≤ edist (F j (σ k) x) (G j x)} else ∅) ≤ tolerance k
      rw [ite_eq_left hjk]
      exact hN k (σ k) (hNσ k) j (mem_range.mpr (Nat.lt_succ_of_le hjk))
    · change μ j (if j ≤ k then {x | tolerance k ≤ edist (F j (σ k) x) (G j x)} else ∅) ≤ tolerance k
      rw [ite_eq_right hjk, measure_empty]
      exact bot_le
  have hsumTol : (∑' k, tolerance k) ≠ ∞ := by
    simpa only [tolerance, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using
      (ENNReal.ofNat_ne_top (n := 2))
  have hsum : (∑' k, μ j (bad k)) ≠ ∞ := ne_top_of_le_ne_top hsumTol (ENNReal.tsum_le_tsum hbad)
  filter_upwards [ae_eventually_notMem hsum] with x hx
  apply EMetric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hε.ne'
  apply eventually_atTop.mp
  filter_upwards [hx, eventually_ge_atTop j, eventually_ge_atTop k] with n hn hjn hkn
  have hnot : ¬ tolerance n ≤ edist (F j (σ n) x) (G j x) := by
    change x ∉ (if j ≤ n then {z | tolerance n ≤ edist (F j (σ n) z) (G j z)} else ∅) at hn
    simpa only [ite_eq_left hjn, mem_ofPred_eq] using hn
  have hpow : tolerance n ≤ tolerance k := by
    change (2 : ℝ≥0∞)⁻¹ ^ n ≤ (2 : ℝ≥0∞)⁻¹ ^ k
    exact pow_le_pow_of_le_one (show (0 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ from bot_le) (ENNReal.inv_le_one.mpr (by norm_num)) hkn
  exact ((lt_of_not_ge hnot).trans_le hpow).trans hk

end VeechDichotomy.CountableConvergenceInMeasure
