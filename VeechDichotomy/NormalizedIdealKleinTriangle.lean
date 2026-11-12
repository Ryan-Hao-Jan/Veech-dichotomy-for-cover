module

public import VeechDichotomy.HorizontalApexTriangles
public import VeechDichotomy.MobiusIdealTriangleArea

/-! The regions whose actual ideal-triangle areas were computed are
literal Klein triangles: the inverse images of the Euclidean hull of
the two finite horizontal vertices and the ideal point i. All coordinate
inequalities and the actual vertices are identified, so intrinsic convexity
and containment of finite subtriangles follow without a geometry oracle. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedIdealKleinTriangle

open Set HyperbolicKleinMap HyperbolicGeodesicHulls
open NormalizedIdealTriangleCoordinates NormalizedTriangleTangents MobiusIdealTriangleArea
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem height_le_iff (z : ℍ) : height z.re ≤ z.im ↔ 1 ≤ Complex.normSq (z : ℂ) := by
  rw [height, Real.sqrt_le_left z.im_pos.le]
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor <;> intro h <;> linarith

theorem point_im_nonneg_iff (z : ℍ) : 0 ≤ (point z).im ↔ height z.re ≤ z.im := by
  rw [height_le_iff]
  change 0 ≤ (denominator z - 2) / denominator z ↔ _
  rw [le_div_iff₀ (denominator_pos z)]
  simp only [zero_mul, denominator]
  constructor <;> intro h <;> linarith

theorem point_im_lt_one (z : ℍ) : (point z).im < 1 := by
  have h : 0 < 1 - (point z).im := by
    rw [one_sub_im]
    exact div_pos (by norm_num) (denominator_pos z)
  linarith

theorem vertical_lower_iff (a : ℝ) (z : ℍ) :
    a ≤ z.re ↔ (1 - (point z).im) * a ≤ (point z).re := by
  rw [one_sub_im]
  change a ≤ z.re ↔ (2 / denominator z) * a ≤ 2 * z.re / denominator z
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (denominator_pos z)]
  constructor <;> intro h <;> linarith

theorem vertical_upper_iff (b : ℝ) (z : ℍ) :
    z.re ≤ b ↔ (point z).re ≤ (1 - (point z).im) * b := by
  rw [one_sub_im]
  change z.re ≤ b ↔ 2 * z.re / denominator z ≤ (2 / denominator z) * b
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (denominator_pos z)]
  constructor <;> intro h <;> linarith

theorem region_mem_iff {a b : ℝ} (hab : a ≤ b) (z : ℍ) :
    z ∈ region a b ↔ point z ∈ HorizontalApexTriangles.planar a b := by
  rw [HorizontalApexTriangles.mem_iff hab]
  constructor
  · rintro ⟨hzx, hzy⟩
    exact ⟨(point_im_nonneg_iff z).mpr hzy, (point_im_lt_one z).le,
      (vertical_lower_iff a z).mp hzx.1, (vertical_upper_iff b z).mp hzx.2⟩
  · rintro ⟨hy, _, hl, hr⟩
    exact ⟨⟨(vertical_lower_iff a z).mpr hl, (vertical_upper_iff b z).mpr hr⟩,
      (point_im_nonneg_iff z).mp hy⟩

theorem region_eq_preimage {a b : ℝ} (hab : a ≤ b) :
    region a b = point ⁻¹' HorizontalApexTriangles.planar a b := by
  ext z
  exact region_mem_iff hab z

theorem image_region {a b : ℝ} (hab : a ≤ b) :
    point '' region a b = Metric.ball (0 : ℂ) 1 ∩ HorizontalApexTriangles.planar a b := by
  rw [region_eq_preimage hab, image_preimage_eq_inter_range, point_range, inter_comm]

theorem geodesicallyConvex_region {a b : ℝ} (hab : a ≤ b) :
    GeodesicallyConvex (region a b) := by
  rw [geodesicallyConvex_iff, image_region hab]
  exact (convex_ball _ _).inter (HorizontalApexTriangles.convex_planar a b)

theorem point_vertex (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    point (vertex x hx₀ hx₁) = (x : ℂ) := by
  have hd : denominator (vertex x hx₀ hx₁) = 2 := by
    rw [denominator_formula]
    have hsq := height_sq hx₀ hx₁
    change (curve x).re ^ 2 + (curve x).im ^ 2 + 1 = 2
    simp only [curve, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, zero_add, sub_zero]
    linarith
  apply Complex.ext
  · change 2 * (vertex x hx₀ hx₁).re / denominator (vertex x hx₀ hx₁) = x
    rw [hd]
    change 2 * (curve x).re / 2 = x
    simp [curve]
  · change (denominator (vertex x hx₀ hx₁) - 2) / denominator (vertex x hx₀ hx₁) = 0
    rw [hd]
    norm_num

theorem finite_triangle_subset {a b : ℝ} (hab : a ≤ b) {p q r : ℍ}
    (hp : p ∈ region a b) (hq : q ∈ region a b) (hr : r ∈ region a b) :
    HyperbolicTriangles.triangle p q r ⊆ region a b :=
  HyperbolicTriangles.triangle_subset (geodesicallyConvex_region hab) hp hq hr

end VeechDichotomy.NormalizedIdealKleinTriangle
