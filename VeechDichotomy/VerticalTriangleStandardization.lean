module

public import VeechDichotomy.HyperbolicCircleNormalization

/-! Every actual triple with an ordered vertical side and third point
to its right is explicitly normalized to the finite triangle model.
The actual circle through the lower and right vertices becomes the
unit semicircle; the upper vertex remains vertically above the lower. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.VerticalTriangleStandardization

open LinearGroup HyperbolicAffineNormalization HyperbolicCircleNormalization MobiusIdealTriangleArea
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def toUnit (u v : ℍ) : SL2 := (matrix (center u v) (radius u v) (radius_pos u v))⁻¹

theorem toUnit_re (u v z : ℍ) : (toUnit u v • z).re = (z.re - center u v) / radius u v :=
  inverse_action_re _ _ (radius_pos u v) z

theorem toUnit_im (u v z : ℍ) : (toUnit u v • z).im = z.im / radius u v :=
  inverse_action_im _ _ (radius_pos u v) z

theorem toUnit_left (u v : ℍ) : Complex.normSq ((toUnit u v • u : ℍ) : ℂ) = 1 :=
  inverse_unit_circle _ _ (radius_pos u v) u (left_incidence u v)

theorem toUnit_right {u v : ℍ} (huv : u.re ≠ v.re) :
    Complex.normSq ((toUnit u v • v : ℍ) : ℂ) = 1 :=
  inverse_unit_circle _ _ (radius_pos u v) v (right_incidence huv)

theorem exists_model (u v w : ℍ) (hvertical : u.re = w.re) (hheight : u.im < w.im) (hright : u.re < v.re) :
    ∃ (F : SL2) (a b : ℝ) (ha : -1 < a) (hb : b < 1) (hab : a < b) (p : ℍ),
      F • u = vertex a ha (hab.trans hb) ∧ F • v = vertex b (ha.trans hab) hb ∧
        F • w = p ∧ p.re = a ∧ 1 < Complex.normSq (p : ℂ) := by
  let F := toUnit u v
  have hU : Complex.normSq ((F • u : ℍ) : ℂ) = 1 := toUnit_left u v
  have hV : Complex.normSq ((F • v : ℍ) : ℂ) = 1 := toUnit_right hright.ne
  obtain ⟨ha₀, ha₁, hA⟩ := unit_vertex (F • u) hU
  obtain ⟨hb₀, hb₁, hB⟩ := unit_vertex (F • v) hV
  have hab : (F • u).re < (F • v).re := by
    rw [toUnit_re, toUnit_re]
    exact (div_lt_div_iff_of_pos_right (radius_pos u v)).mpr (sub_lt_sub_right hright _)
  have hpRe : (F • w).re = (F • u).re := by
    rw [toUnit_re, toUnit_re, ← hvertical]
  have hpIm : (F • u).im < (F • w).im := by
    rw [toUnit_im, toUnit_im]
    exact (div_lt_div_iff_of_pos_right (radius_pos u v)).mpr hheight
  have hpNorm : 1 < Complex.normSq ((F • w : ℍ) : ℂ) := by
    simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hU ⊢
    rw [hpRe]
    nlinarith [hpIm, (F • u).im_pos, (F • w).im_pos]
  exact ⟨F, (F • u).re, (F • v).re, ha₀, hb₁, hab, F • w, hA, hB, rfl, hpRe, hpNorm⟩

end VeechDichotomy.VerticalTriangleStandardization
