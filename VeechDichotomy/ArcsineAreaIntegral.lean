module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith

/-! The actual horizontal area integral above a unit semicircle.
On each strict subinterval of (-1,1), the positive height sqrt(1-x^2)
gives a continuous integrable reciprocal, and the proved arcsine
derivative plus the fundamental theorem compute both real and
nonnegative Lebesgue integrals. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ArcsineAreaIntegral

open Set MeasureTheory
open scoped ENNReal

def density (x : ℝ) : ℝ := 1 / Real.sqrt (1 - x ^ 2)

theorem height_pos {a b x : ℝ} (ha : -1 < a) (hb : b < 1) (hx : x ∈ Icc a b) :
    0 < Real.sqrt (1 - x ^ 2) := by
  apply Real.sqrt_pos.mpr
  have hleft : 0 < 1 + x := by linarith only [ha, hx.1]
  have hright : 0 < 1 - x := by linarith only [hb, hx.2]
  have hp := mul_pos hleft hright
  nlinarith only [hp]

theorem continuousOn_density {a b : ℝ} (ha : -1 < a) (hb : b < 1) : ContinuousOn density (Icc a b) := by
  have hh : Continuous (fun x : ℝ => Real.sqrt (1 - x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
  exact continuousOn_const.div hh.continuousOn (fun x hx => (height_pos ha hb hx).ne')

theorem intervalIntegrable_density {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    IntervalIntegrable density volume a b := (continuousOn_density ha hb).intervalIntegrable_of_Icc hab

theorem interval_integral {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    ∫ x in a..b, density x = Real.arcsin b - Real.arcsin a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (intervalIntegrable_density ha hb hab)
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact Real.hasDerivAt_arcsin (ha.trans_le hx.1).ne' (hx.2.trans_lt hb).ne

theorem integral_Icc {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    ∫ x in Icc a b, density x = Real.arcsin b - Real.arcsin a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact interval_integral ha hb hab

theorem lintegral_Icc {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    ∫⁻ x in Icc a b, ENNReal.ofReal (density x) = ENNReal.ofReal (Real.arcsin b - Real.arcsin a) := by
  have hint : IntegrableOn density (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (intervalIntegrable_density ha hb hab)
  have hnn : ∀ x : ℝ, 0 ≤ density x := fun x => div_nonneg zero_le_one (Real.sqrt_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn), integral_Icc ha hb hab]

end VeechDichotomy.ArcsineAreaIntegral
