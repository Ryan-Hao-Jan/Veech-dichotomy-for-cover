module

public import VeechDichotomy.MobiusIdealTriangleArea

/-! The genuine nonnegative triangle angle deficit equals actual REAL
hyperbolic area, not merely its extended-nonnegative clipping. Monotonicity
of actual arcsine proves the sign and the proved actual volume formulas
give the literal real values, also after actual SL2 transport. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.IdealTriangleRealArea

open LinearGroup NormalizedIdealTriangleCoordinates NormalizedIdealTriangleAngles
open MobiusIdealTriangleArea MeasureTheory
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

def deficit (a b : ℝ) : ℝ := Real.pi - leftAngle a - rightAngle b

theorem deficit_eq {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    deficit a b = Real.arcsin b - Real.arcsin a := by
  rw [deficit, leftAngle_formula ha (hab.trans_lt hb), rightAngle_formula (ha.trans_le hab) hb]
  ring

theorem deficit_nonneg {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) : 0 ≤ deficit a b := by
  rw [deficit_eq ha hb hab]
  exact sub_nonneg.mpr (Real.monotone_arcsin hab)

theorem real_area_formula {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    (volume (region a b)).toReal = deficit a b := by
  rw [area_formula_angles ha hb hab]
  change (ENNReal.ofReal (deficit a b)).toReal = deficit a b
  exact ENNReal.toReal_ofReal (deficit_nonneg ha hb hab)

theorem image_deficit_eq (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    Real.pi - leftImageAngle A a ha (hab.trans_lt hb) - rightImageAngle A b (ha.trans_le hab) hb = deficit a b := by
  rw [leftImageAngle_eq, rightImageAngle_eq]
  rfl

theorem image_deficit_nonneg (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    0 ≤ Real.pi - leftImageAngle A a ha (hab.trans_lt hb) - rightImageAngle A b (ha.trans_le hab) hb := by
  rw [image_deficit_eq A ha hb hab]
  exact deficit_nonneg ha hb hab

theorem image_real_area_formula (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    (volume (imageRegion A a b)).toReal =
      Real.pi - leftImageAngle A a ha (hab.trans_lt hb) - rightImageAngle A b (ha.trans_le hab) hb := by
  rw [image_deficit_eq A ha hb hab, area_imageRegion]
  exact real_area_formula ha hb hab

theorem full_real_area : (volume NormalizedFullIdealTriangleArea.fullRegion).toReal = Real.pi := by
  rw [NormalizedFullIdealTriangleArea.area_full, ENNReal.toReal_ofReal Real.pi_pos.le]

theorem full_image_real_area (A : SL2) :
    (volume ((fun z : ℍ => A • z) '' NormalizedFullIdealTriangleArea.fullRegion)).toReal = Real.pi := by
  rw [area_fullIdeal_image, ENNReal.toReal_ofReal Real.pi_pos.le]

end VeechDichotomy.IdealTriangleRealArea
