module

public import VeechDichotomy.HyperbolicIntrinsicAngles

/-! The fixed endpoint direction vectors are actual geodesic tangent
directions: circle incidences give a literal scalar multiple of the
actual circle tangent; real-part ordering proves its sign. Equal real
parts give the correctly oriented actual vertical tangent. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicEndpointTangents

open HyperbolicDirectionVectors
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def circleTangent (c : ℝ) (a : ℍ) : ℂ := ⟨a.im, c - a.re⟩

theorem circle_direction (c r : ℝ) (a b : ℍ)
    (ha : Complex.normSq ((a : ℂ) - (c : ℂ)) = r ^ 2)
    (hb : Complex.normSq ((b : ℂ) - (c : ℂ)) = r ^ 2) :
    direction a b = ((b.re - a.re) / a.im) • circleTangent c a := by
  have hnum : (b.re - a.re) ^ 2 + b.im ^ 2 - a.im ^ 2 = 2 * (b.re - a.re) * (c - a.re) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero] at ha hb
    nlinarith only [ha, hb]
  rw [Complex.real_smul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change b.re - a.re = ((b.re - a.re) / a.im) * a.im
    exact (div_mul_cancel₀ _ a.im_ne_zero).symm
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    change verticalCoefficient a b = ((b.re - a.re) / a.im) * (c - a.re)
    rw [verticalCoefficient, hnum]
    field_simp [a.im_ne_zero]

theorem circle_right (c r : ℝ) (a b : ℍ)
    (ha : Complex.normSq ((a : ℂ) - (c : ℂ)) = r ^ 2)
    (hb : Complex.normSq ((b : ℂ) - (c : ℂ)) = r ^ 2) (hre : a.re < b.re) :
    ∃ k : ℝ, 0 < k ∧ direction a b = k • circleTangent c a :=
  ⟨(b.re - a.re) / a.im, div_pos (sub_pos.mpr hre) a.im_pos, circle_direction c r a b ha hb⟩

theorem circle_left (c r : ℝ) (a b : ℍ)
    (ha : Complex.normSq ((a : ℂ) - (c : ℂ)) = r ^ 2)
    (hb : Complex.normSq ((b : ℂ) - (c : ℂ)) = r ^ 2) (hre : b.re < a.re) :
    ∃ k : ℝ, 0 < k ∧ direction a b = k • (-circleTangent c a) := by
  refine ⟨(a.re - b.re) / a.im, div_pos (sub_pos.mpr hre) a.im_pos, ?_⟩
  rw [circle_direction c r a b ha hb, smul_neg]
  have he : (b.re - a.re) / a.im = -((a.re - b.re) / a.im) := by ring
  rw [he, neg_smul]

theorem vertical_direction (a b : ℍ) (hre : a.re = b.re) :
    direction a b = ((b.im ^ 2 - a.im ^ 2) / (2 * a.im)) • (Complex.I : ℂ) := by
  rw [Complex.real_smul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, direction]
    exact sub_eq_zero.mpr hre.symm
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero]
    change verticalCoefficient a b = (b.im ^ 2 - a.im ^ 2) / (2 * a.im)
    simp only [verticalCoefficient, hre, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]

theorem vertical_up (a b : ℍ) (hre : a.re = b.re) (him : a.im < b.im) :
    ∃ k : ℝ, 0 < k ∧ direction a b = k • (Complex.I : ℂ) := by
  refine ⟨(b.im ^ 2 - a.im ^ 2) / (2 * a.im), ?_, vertical_direction a b hre⟩
  apply div_pos _ (mul_pos (by norm_num) a.im_pos)
  nlinarith [a.im_pos, b.im_pos]

theorem vertical_down (a b : ℍ) (hre : a.re = b.re) (him : b.im < a.im) :
    ∃ k : ℝ, 0 < k ∧ direction a b = k • (-Complex.I : ℂ) := by
  refine ⟨(a.im ^ 2 - b.im ^ 2) / (2 * a.im), ?_, ?_⟩
  · apply div_pos _ (mul_pos (by norm_num) a.im_pos)
    nlinarith [a.im_pos, b.im_pos]
  · rw [vertical_direction a b hre, smul_neg]
    have he : (b.im ^ 2 - a.im ^ 2) / (2 * a.im) = -((a.im ^ 2 - b.im ^ 2) / (2 * a.im)) := by ring
    rw [he, neg_smul]

theorem circleTangent_graph (c r : ℝ) (a : ℍ)
    (ha : Complex.normSq ((a : ℂ) - (c : ℂ)) = r ^ 2) :
    circleTangent c a = CircularTriangleTangents.rightwardTangent c r a.re := by
  apply Complex.ext
  · exact (CircularTriangleTangents.height_eq_im c r a ha).symm
  · rfl

end VeechDichotomy.HyperbolicEndpointTangents
