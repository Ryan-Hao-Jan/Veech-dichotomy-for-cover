module

public import VeechDichotomy.CircularTriangleTangents
public import VeechDichotomy.NormalizedFiniteTriangleArea

/-! Actual parameter bounds, orientation and circle incidences for the
constructed upper circle of a normalized finite triangle. In particular,
its normalized right endpoint is strictly larger than the base endpoint;
the sign is derived from the radius equation and negative center. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedFiniteTriangleParameters

open NormalizedFiniteTriangleArea CircularIdealTriangleArea MobiusIdealTriangleArea
open NormalizedTriangleTangents
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem radius_bounds {c r b : ℝ} (hc : c < 0) (hr : 0 < r) (hb₀ : -1 < b) (hb₁ : b < 1)
    (hrad : r ^ 2 = 1 + c ^ 2 - 2 * c * b) : 1 + c ≤ r ∧ r ≤ 1 - c := by
  constructor
  · by_cases hpos : 0 ≤ 1 + c
    · apply (sq_le_sq₀ hpos hr.le).mp
      have hm := mul_nonpos_of_nonpos_of_nonneg hc.le (show 0 ≤ b + 1 by linarith)
      nlinarith only [hrad, hm]
    · exact (le_of_not_ge hpos).trans hr.le
  · apply (sq_le_sq₀ hr.le (show 0 ≤ 1 - c by linarith)).mp
    have hm := mul_nonneg_of_nonpos_of_nonpos hc.le (sub_nonpos.mpr hb₁.le)
    nlinarith only [hrad, hm]

theorem right_coord_gt {c r b : ℝ} (hc : c < 0) (hr : 0 < r) (hb₀ : -1 < b) (hb₁ : b < 1)
    (hrad : r ^ 2 = 1 + c ^ 2 - 2 * c * b) : b < coord c r b := by
  obtain ⟨hlo, hhi⟩ := radius_bounds hc hr hb₀ hb₁ hrad
  apply (lt_div_iff₀ hr).mpr
  by_cases hb : 0 ≤ b
  · have hprod := mul_le_mul_of_nonneg_left (show r - 1 ≤ -c by linarith) hb
    have hstrict := mul_lt_mul_of_pos_right hb₁ (neg_pos.mpr hc)
    nlinarith only [hprod, hstrict]
  · have hprod := mul_le_mul_of_nonpos_left (show c ≤ r - 1 by linarith) (le_of_not_ge hb)
    have hstrict := mul_lt_mul_of_neg_right hb₀ hc
    nlinarith only [hprod, hstrict]

def upperCoord (a b : ℝ) (p : ℍ) (x : ℝ) : ℝ := coord (center a b p) (radius a b p) x

theorem upper_left_bounds {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : -1 < upperCoord a b p a ∧ upperCoord a b p a < 1 := by
  exact ⟨coord_left (radius_pos a b p) (left_diameter p hpre),
    coord_right (radius_pos a b p) (hab.trans (right_diameter ha hb hab p hpre))⟩

theorem upper_right_bounds {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : -1 < upperCoord a b p b ∧ upperCoord a b p b < 1 := by
  exact ⟨coord_left (radius_pos a b p) ((left_diameter p hpre).trans hab),
    coord_right (radius_pos a b p) (right_diameter ha hb hab p hpre)⟩

theorem upper_right_gt {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) : b < upperCoord a b p b :=
  right_coord_gt (center_neg hab hp) (radius_pos a b p) (ha.trans hab) hb (radius_formula hab p hpre)

theorem unit_vertex_normSq (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    Complex.normSq (vertex x hx₀ hx₁ : ℂ) = 1 := by
  have hs := NormalizedTriangleTangents.height_sq hx₀ hx₁
  simp only [vertex_coe, NormalizedTriangleTangents.curve, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero]
  linarith

theorem right_circle_incidence {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) :
    Complex.normSq ((vertex b (ha.trans hab) hb : ℂ) - (center a b p : ℂ)) = radius a b p ^ 2 := by
  have hs := NormalizedTriangleTangents.height_sq (ha.trans hab) hb
  rw [radius_formula hab p hpre]
  simp only [vertex_coe, NormalizedTriangleTangents.curve, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero,
    zero_add, sub_zero]
  nlinarith only [hs]

theorem upper_height_left {a b : ℝ} (p : ℍ) (hpre : p.re = a) :
    CircularTriangleTangents.height (center a b p) (radius a b p) a = p.im := by
  rw [← hpre]
  exact CircularTriangleTangents.height_eq_im _ _ p (circle_incidence p.re b p)

theorem upper_height_right {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) :
    CircularTriangleTangents.height (center a b p) (radius a b p) b =
      NormalizedIdealTriangleCoordinates.height b := by
  have h := CircularTriangleTangents.height_eq_im _ _ (vertex b (ha.trans hab) hb)
    (right_circle_incidence ha hb hab p hpre)
  simpa [vertex, NormalizedTriangleTangents.curve] using h

end VeechDichotomy.NormalizedFiniteTriangleParameters
