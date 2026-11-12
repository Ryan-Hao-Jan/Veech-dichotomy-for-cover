module

public import VeechDichotomy.NormalizedFiniteTriangleRegions

/-! A complete actual area computation for normalized finite triangles.
The upper circle is constructed from the genuine upper vertex, its sign,
positive radius and both diameter bounds are proved, and the literal
triangle equals the closed difference of two already measured ideal
regions. No circle parameters or containment facts are assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedFiniteTriangleArea

open LinearGroup Set MeasureTheory HyperbolicTriangles MobiusIdealTriangleArea
open CircularTriangleDifferences CircularIdealTriangleArea NormalizedFiniteTriangleRegions
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

def center (a b : ℝ) (p : ℍ) : ℝ := (Complex.normSq (p : ℂ) - 1) / (2 * (a - b))
def radius (a b : ℝ) (p : ℍ) : ℝ := ‖(p : ℂ) - (center a b p : ℂ)‖

theorem center_neg {a b : ℝ} (hab : a < b) {p : ℍ} (hp : 1 < Complex.normSq (p : ℂ)) :
    center a b p < 0 :=
  div_neg_of_pos_of_neg (sub_pos.mpr hp) (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hab))

theorem radius_pos (a b : ℝ) (p : ℍ) : 0 < radius a b p := by
  apply norm_pos_iff.mpr
  intro he
  have hi := congrArg Complex.im he
  have hz : p.im = 0 := by simpa using hi
  exact p.im_ne_zero hz

theorem circle_incidence (a b : ℝ) (p : ℍ) :
    Complex.normSq ((p : ℂ) - (center a b p : ℂ)) = radius a b p ^ 2 :=
  (Complex.sq_norm _).symm

theorem radius_formula {a b : ℝ} (hab : a < b) (p : ℍ) (hpre : p.re = a) :
    radius a b p ^ 2 = 1 + center a b p ^ 2 - 2 * center a b p * b := by
  have hden : 2 * (a - b) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab.ne)
  have hc : center a b p * (2 * (a - b)) = Complex.normSq (p : ℂ) - 1 :=
    div_mul_cancel₀ _ hden
  have hn := circle_incidence a b p
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero, hpre] at hc hn
  nlinarith only [hc, hn]

theorem left_diameter {a b : ℝ} (p : ℍ) (hpre : p.re = a) :
    center a b p - radius a b p < a := by
  have hn := circle_incidence a b p
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero, hpre] at hn
  have hs : (a - center a b p) ^ 2 < radius a b p ^ 2 := by
    nlinarith only [hn, sq_pos_of_pos p.im_pos]
  have h := (abs_lt_of_sq_lt_sq' hs (radius_pos a b p).le).1
  linarith

theorem right_diameter {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : b < center a b p + radius a b p := by
  have hsq : b ^ 2 < 1 := by nlinarith [ha.trans hab]
  have hr := radius_formula hab p hpre
  have hs : (b - center a b p) ^ 2 < radius a b p ^ 2 := by nlinarith only [hr, hsq]
  have h := (abs_lt_of_sq_lt_sq' hs (radius_pos a b p).le).2
  linarith

theorem real_area_formula {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    (volume (triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p)).toReal =
      (Real.arcsin b - Real.arcsin a) -
        (Real.arcsin (coord (center a b p) (radius a b p) b) -
          Real.arcsin (coord (center a b p) (radius a b p) a)) := by
  have hc := center_neg hab hp
  have hr := radius_formula hab p hpre
  have hga : 0 ≤ gap 0 1 (center a b p) (radius a b p) a := by
    dsimp only [gap]
    rw [hr]
    have hm := mul_nonneg_of_nonpos_of_nonpos hc.le (sub_nonpos.mpr hab.le)
    nlinarith only [hm]
  have hgb : 0 ≤ gap 0 1 (center a b p) (radius a b p) b := by
    dsimp only [gap]
    rw [hr]
    ring_nf
    exact le_rfl
  rw [triangle_eq_closedBand ha hb hab p hpre hp _ _ hc hr (circle_incidence a b p)]
  have h := real_area_band 0 1 (center a b p) (radius a b p) (by norm_num) (radius_pos a b p)
    (by simpa using ha) (by simpa using hb) (left_diameter p hpre) (right_diameter ha hb hab p hpre)
    hab.le hga hgb
  simpa only [areaValue, coord, sub_zero, div_one] using h

theorem mapped_real_area_formula (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    (volume (triangle (A • vertex a ha (hab.trans hb)) (A • vertex b (ha.trans hab) hb) (A • p))).toReal =
      (Real.arcsin b - Real.arcsin a) -
        (Real.arcsin (coord (center a b p) (radius a b p) b) -
          Real.arcsin (coord (center a b p) (radius a b p) a)) := by
  rw [← image_triangle_smul]
  have hm : volume ((fun z : ℍ => A • z) '' triangle (vertex a ha (hab.trans hb))
      (vertex b (ha.trans hab) hb) p) =
      volume (triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p) :=
    measure_smul (volume : Measure ℍ) A _
  rw [hm]
  exact real_area_formula ha hb hab p hpre hp

end VeechDichotomy.NormalizedFiniteTriangleArea
