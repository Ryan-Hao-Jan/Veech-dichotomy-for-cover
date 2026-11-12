module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual inverse-square vertical density integral needed for
hyperbolic triangle area. Integrability and the improper integral follow
from the proved real-power integral theorem; nonnegative Lebesgue
integrals are identified with the actual finite real integrals. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.InverseSquareAreaIntegral

open Set MeasureTheory
open scoped ENNReal

def density (y : ℝ) : ℝ := (1 / y) ^ 2

theorem density_eq_rpow (y : ℝ) : density y = y ^ (-2 : ℝ) := by
  norm_num [density, one_div]

theorem density_nonneg (y : ℝ) : 0 ≤ density y := sq_nonneg _

theorem integrable_density_Ioi {h : ℝ} (hh : 0 < h) : IntegrableOn density (Ioi h) := by
  have hr : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi h) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hh
  exact hr.congr_fun (fun y _ => (density_eq_rpow y).symm) measurableSet_Ioi

theorem integral_density_Ioi {h : ℝ} (hh : 0 < h) : ∫ y in Ioi h, density y = 1 / h := by
  simp_rw [density_eq_rpow]
  have hi := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hh
  norm_num [Real.rpow_neg_one] at hi ⊢
  exact hi

theorem lintegral_density_Ioi {h : ℝ} (hh : 0 < h) :
    ∫⁻ y in Ioi h, ENNReal.ofReal (density y) = ENNReal.ofReal (1 / h) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_density_Ioi hh)
    (Filter.Eventually.of_forall density_nonneg), integral_density_Ioi hh]

theorem lintegral_density_Ici {h : ℝ} (hh : 0 < h) :
    ∫⁻ y in Ici h, ENNReal.ofReal (density y) = ENNReal.ofReal (1 / h) := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  exact lintegral_density_Ioi hh

end VeechDichotomy.InverseSquareAreaIntegral
