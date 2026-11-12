module

public import VeechDichotomy.HyperbolicAffineNormalization
public import VeechDichotomy.NormalizedIdealKleinTriangle

/-! Actual coordinate area formulas for one-ideal regions above any
positive real-centered semicircle. The endpoints are arbitrary real
coordinates strictly inside that circle's horizontal diameter. The proved
affine SL2 action supplies literal region equality and area invariance. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CircularIdealTriangleArea

open Set MeasureTheory HyperbolicAffineNormalization HyperbolicGeodesicHulls
open scoped UpperHalfPlane ENNReal

def coord (c r x : ℝ) : ℝ := (x - c) / r

theorem coord_back (c r : ℝ) (hr : 0 < r) (x : ℝ) : r * coord c r x + c = x := by
  dsimp only [coord]
  field_simp [hr.ne']
  ring

theorem coord_left {c r a : ℝ} (hr : 0 < r) (ha : c - r < a) : -1 < coord c r a := by
  apply (lt_div_iff₀ hr).mpr
  linarith

theorem coord_right {c r b : ℝ} (hr : 0 < r) (hb : b < c + r) : coord c r b < 1 := by
  apply (div_lt_iff₀ hr).mpr
  linarith

theorem coord_mono (c : ℝ) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b) :
    coord c r a ≤ coord c r b :=
  (div_le_div_iff_of_pos_right hr).mpr (sub_le_sub_right hab c)

theorem normalized_image (c r : ℝ) (hr : 0 < r) (a b : ℝ) :
    MobiusIdealTriangleArea.imageRegion (matrix c r hr) (coord c r a) (coord c r b) =
      circleRegion c r a b := by
  rw [HyperbolicAffineNormalization.image_region, coord_back c r hr a, coord_back c r hr b]

def areaValue (c r a b : ℝ) : ℝ := Real.arcsin (coord c r b) - Real.arcsin (coord c r a)

theorem areaValue_nonneg (c : ℝ) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ areaValue c r a b :=
  sub_nonneg.mpr (Real.monotone_arcsin (coord_mono c hr hab))

theorem area_formula (c r : ℝ) (hr : 0 < r) {a b : ℝ}
    (ha : c - r < a) (hb : b < c + r) (hab : a ≤ b) :
    volume (circleRegion c r a b) = ENNReal.ofReal (areaValue c r a b) := by
  have h := HyperbolicAffineNormalization.area_circleRegion c r hr
    (coord_left hr ha) (coord_right hr hb) (coord_mono c hr hab)
  rw [coord_back c r hr a, coord_back c r hr b] at h
  exact h

theorem real_area_formula (c r : ℝ) (hr : 0 < r) {a b : ℝ}
    (ha : c - r < a) (hb : b < c + r) (hab : a ≤ b) :
    (volume (circleRegion c r a b)).toReal = areaValue c r a b := by
  rw [area_formula c r hr ha hb hab, ENNReal.toReal_ofReal (areaValue_nonneg c hr hab)]

theorem area_lt_top (c r : ℝ) (hr : 0 < r) {a b : ℝ}
    (ha : c - r < a) (hb : b < c + r) (hab : a ≤ b) : volume (circleRegion c r a b) < ⊤ := by
  rw [area_formula c r hr ha hb hab]
  exact ENNReal.ofReal_lt_top

theorem geodesicallyConvex_circleRegion (c r : ℝ) (hr : 0 < r) {a b : ℝ} (hab : a ≤ b) :
    GeodesicallyConvex (circleRegion c r a b) := by
  rw [← normalized_image c r hr a b]
  exact geodesicallyConvex_smul (matrix c r hr)
    (NormalizedIdealKleinTriangle.geodesicallyConvex_region (coord_mono c hr hab))

end VeechDichotomy.CircularIdealTriangleArea
