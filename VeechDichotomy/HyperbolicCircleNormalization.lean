module

public import VeechDichotomy.HyperbolicTripleNormalization
public import VeechDichotomy.CircularGeodesicArcs

/-! Actual circle normalization of two upper-half-plane points with
distinct real parts. The explicit real center and strictly positive
radius give exact incidences. The genuine inverse affine SL2 action
sends this circle to the unit semicircle, with literal vertex coordinates. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicCircleNormalization

open LinearGroup HyperbolicAffineNormalization MobiusIdealTriangleArea
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def center (u v : ℍ) : ℝ :=
  (Complex.normSq (u : ℂ) - Complex.normSq (v : ℂ)) / (2 * (u.re - v.re))

def radius (u v : ℍ) : ℝ := ‖(u : ℂ) - (center u v : ℂ)‖

theorem radius_pos (u v : ℍ) : 0 < radius u v := by
  apply norm_pos_iff.mpr
  intro he
  have hi := congrArg Complex.im he
  exact u.im_ne_zero (by simpa using hi)

theorem left_incidence (u v : ℍ) :
    Complex.normSq ((u : ℂ) - (center u v : ℂ)) = radius u v ^ 2 :=
  (Complex.sq_norm _).symm

theorem right_incidence {u v : ℍ} (huv : u.re ≠ v.re) :
    Complex.normSq ((v : ℂ) - (center u v : ℂ)) = radius u v ^ 2 := by
  rw [← left_incidence]
  dsimp only [center]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp [sub_ne_zero.mpr huv]
  ring

theorem inverse_action_complex (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (((matrix c r hr)⁻¹ • z : ℍ) : ℂ) = ((z : ℂ) - (c : ℂ)) / (r : ℂ) := by
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hr.ne')).mpr
  have h := action_complex c r hr ((matrix c r hr)⁻¹ • z)
  rw [smul_inv_smul] at h
  rw [mul_comm]
  exact eq_sub_iff_add_eq.mpr h.symm

theorem inverse_action_re (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    ((matrix c r hr)⁻¹ • z).re = (z.re - c) / r := by
  rw [← UpperHalfPlane.coe_re, inverse_action_complex, Complex.div_ofReal_re]
  simp

theorem inverse_action_im (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    ((matrix c r hr)⁻¹ • z).im = z.im / r := by
  rw [← UpperHalfPlane.coe_im, inverse_action_complex, Complex.div_ofReal_im]
  simp

theorem inverse_unit_circle (c r : ℝ) (hr : 0 < r) (z : ℍ)
    (hz : Complex.normSq ((z : ℂ) - (c : ℂ)) = r ^ 2) :
    Complex.normSq (((matrix c r hr)⁻¹ • z : ℍ) : ℂ) = 1 := by
  have h := action_normSq c r hr ((matrix c r hr)⁻¹ • z)
  rw [smul_inv_smul, hz] at h
  have hp : r ^ 2 * (Complex.normSq (((matrix c r hr)⁻¹ • z : ℍ) : ℂ) - 1) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hr.ne'))

theorem unit_vertex (z : ℍ) (hz : Complex.normSq (z : ℂ) = 1) :
    ∃ (hx₀ : -1 < z.re) (hx₁ : z.re < 1), z = vertex z.re hx₀ hx₁ := by
  have hn := hz
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn
  have hs : z.re ^ 2 < 1 ^ 2 := by nlinarith only [hn, sq_pos_of_pos z.im_pos]
  obtain ⟨hx₀, hx₁⟩ := abs_lt_of_sq_lt_sq' hs zero_le_one
  refine ⟨hx₀, hx₁, ?_⟩
  apply UpperHalfPlane.ext_re_im
  · simp [vertex, NormalizedTriangleTangents.curve]
  · have hh : NormalizedIdealTriangleCoordinates.height z.re = z.im := by
      change Real.sqrt (1 - z.re ^ 2) = z.im
      rw [show 1 - z.re ^ 2 = z.im ^ 2 by linarith only [hn], Real.sqrt_sq z.im_pos.le]
    simpa [vertex, NormalizedTriangleTangents.curve] using hh.symm

end VeechDichotomy.HyperbolicCircleNormalization
