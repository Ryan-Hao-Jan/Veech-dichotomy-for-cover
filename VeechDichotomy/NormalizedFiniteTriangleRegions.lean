module

public import VeechDichotomy.KleinCircleSupports

/-! A genuine finite triangle with a vertical side and lower unit-circle
side is exactly the closed region between that unit semicircle and the
circle through its upper and right vertices. The actual Klein triangle
half-plane formula proves literal set equality, including all boundaries.
The assumptions state ordinary coordinates and circle incidences only. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedFiniteTriangleRegions

open Set HyperbolicKleinMap HyperbolicGeodesicHulls HyperbolicTriangles
open MobiusIdealTriangleArea NormalizedIdealKleinTriangle HyperbolicAffineNormalization
open CircularTriangleDifferences KleinCircleSupports
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem positive_mul_nonpos {a b : ℝ} (ha : 0 < a) : a * b ≤ 0 ↔ b ≤ 0 := by
  simpa only [mul_zero] using
    (mul_le_mul_iff_of_pos_left ha : a * b ≤ a * 0 ↔ b ≤ 0)

theorem mem_triangle_iff {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ))
    (c r : ℝ) (hc : c < 0) (hrad : r ^ 2 = 1 + c ^ 2 - 2 * c * b)
    (hpc : Complex.normSq ((p : ℂ) - (c : ℂ)) = r ^ 2) (z : ℍ) :
    z ∈ triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p ↔
      z.re ∈ Icc a b ∧ 1 ≤ Complex.normSq (z : ℂ) ∧
        Complex.normSq ((z : ℂ) - (c : ℂ)) ≤ r ^ 2 := by
  let v := (point p).im
  let q := (point p).re
  let x := (point z).re
  let y := (point z).im
  have hv : 0 < v := by
    change 0 < (denominator p - 2) / denominator p
    apply div_pos _ (denominator_pos p)
    dsimp only [denominator]
    linarith
  have hq : q = a * (1 - v) := by
    have hl := (vertical_lower_iff a p).mp hpre.ge
    have hu := (vertical_upper_iff a p).mp hpre.le
    simpa only [q, v, mul_comm] using le_antisymm hu hl
  have hcp := (circle_eq_iff c r b hrad p).mp hpc
  change (-c) * (q - b) + (1 - c * b) * v = 0 at hcp
  have hleft : (v - y) * a + y * q ≤ v * x ↔ (1 - y) * a ≤ x := by
    have hid : v * x - ((v - y) * a + y * q) = v * (x - (1 - y) * a) := by
      rw [hq]
      ring
    calc
      _ ↔ 0 ≤ v * x - ((v - y) * a + y * q) := sub_nonneg.symm
      _ ↔ 0 ≤ v * (x - (1 - y) * a) := by rw [hid]
      _ ↔ 0 ≤ x - (1 - y) * a := mul_nonneg_iff_of_pos_left hv
      _ ↔ _ := sub_nonneg
  have hright : v * x ≤ (v - y) * b + y * q ↔ support c b (point z) ≤ 0 := by
    have hid : (-c) * (v * x - ((v - y) * b + y * q)) = v * support c b (point z) := by
      change (-c) * (v * x - ((v - y) * b + y * q)) = v * ((-c) * (x - b) + (1 - c * b) * y)
      linear_combination -y * hcp
    calc
      _ ↔ v * x - ((v - y) * b + y * q) ≤ 0 := sub_nonpos.symm
      _ ↔ (-c) * (v * x - ((v - y) * b + y * q)) ≤ 0 :=
        (positive_mul_nonpos (neg_pos.mpr hc)).symm
      _ ↔ v * support c b (point z) ≤ 0 := by rw [hid]
      _ ↔ _ := positive_mul_nonpos hv
  have htri : z ∈ triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p ↔
      0 ≤ y ∧ (v - y) * a + y * q ≤ v * x ∧ v * x ≤ (v - y) * b + y * q := by
    change point z ∈ convexHull ℝ (point '' {vertex a ha (hab.trans hb), vertex b (ha.trans hab) hb, p}) ↔ _
    rw [image_insert_eq, image_insert_eq, image_singleton, point_vertex, point_vertex]
    exact EuclideanTriangleCoordinates.mem_triangle_iff_halfPlanes hab (point p) (point z) hv
  rw [htri, hleft, hright]
  constructor
  · rintro ⟨hy, hl, hu⟩
    have hleftz : a ≤ z.re := (vertical_lower_iff a z).mpr hl
    have hunit : 1 ≤ Complex.normSq (z : ℂ) :=
      (height_le_iff z).mp ((point_im_nonneg_iff z).mp hy)
    have hcircle := (circle_le_iff c r b hrad z).mpr hu
    have hrightz : z.re ≤ b := by
      have hnu := hcircle
      have hnl := hunit
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero] at hnu hnl
      have hprod : (-2 * c) * (z.re - b) ≤ 0 := by nlinarith only [hnu, hnl, hrad]
      have hpos : 0 < -2 * c := by linarith
      exact sub_nonpos.mp ((positive_mul_nonpos hpos).mp hprod)
    exact ⟨⟨hleftz, hrightz⟩, hunit, hcircle⟩
  · rintro ⟨hzx, hunit, hcircle⟩
    exact ⟨(point_im_nonneg_iff z).mpr ((height_le_iff z).mpr hunit),
      (vertical_lower_iff a z).mp hzx.1, (circle_le_iff c r b hrad z).mp hcircle⟩

theorem triangle_eq_closedBand {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ))
    (c r : ℝ) (hc : c < 0) (hrad : r ^ 2 = 1 + c ^ 2 - 2 * c * b)
    (hpc : Complex.normSq ((p : ℂ) - (c : ℂ)) = r ^ 2) :
    triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p =
      closedBand 0 1 c r a b := by
  ext z
  rw [mem_triangle_iff ha hb hab p hpre hp c r hc hrad hpc z]
  simp only [closedBand, circleRegion, mem_ofPred_eq, Complex.ofReal_zero, sub_zero, one_pow]
  exact and_assoc.symm

end VeechDichotomy.NormalizedFiniteTriangleRegions
