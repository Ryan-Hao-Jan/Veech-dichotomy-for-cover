module

public import VeechDichotomy.DirichletCornerPolygonOrder

/-! Explicit orientation-preserving coordinates at an exposed root.
A genuine nonzero exposing functional gives positive horizontal
coordinates for every other point. Actual slopes order their rays, and
equal slopes give an actual positive scalar relation between the rays. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ExposedRootCoordinates

open ComplexOrientedTriangles

set_option backward.isDefEq.respectTransparency false

theorem functional_representation (L : ℂ →L[ℝ] ℝ) (z : ℂ) : L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

def frame (L : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (-L) + Complex.I •
    (Complex.ofRealCLM.comp ((L Complex.I) • Complex.reCLM - (L 1) • Complex.imCLM))

theorem frame_re (L : ℂ →L[ℝ] ℝ) (z : ℂ) : (frame L z).re = -L z := by simp [frame]
theorem frame_im (L : ℂ →L[ℝ] ℝ) (z : ℂ) : (frame L z).im = L Complex.I * z.re - L 1 * z.im := by
  simp [frame]

def scale (L : ℂ →L[ℝ] ℝ) : ℝ := (L 1) ^ 2 + (L Complex.I) ^ 2

theorem scale_pos {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) : 0 < scale L := by
  by_contra hn
  have hnon : scale L ≤ 0 := le_of_not_gt hn
  have h₁ : L 1 = 0 := by dsimp only [scale] at hnon; nlinarith [sq_nonneg (L Complex.I)]
  have hI : L Complex.I = 0 := by dsimp only [scale] at hnon; nlinarith [sq_nonneg (L 1)]
  apply hL
  ext z
  rw [functional_representation, h₁, hI]
  simp

theorem frame_cross (L : ℂ →L[ℝ] ℝ) (u v : ℂ) : cross (frame L u) (frame L v) = scale L * cross u v := by
  simp only [cross, frame_re, frame_im]
  rw [functional_representation L u, functional_representation L v]
  dsimp only [scale]
  ring

theorem frame_injective {L : ℂ →L[ℝ] ℝ} (hL : L ≠ 0) : Function.Injective (frame L) := by
  intro u v he
  have hz : frame L (u - v) = 0 := by rw [map_sub, he, sub_self]
  have h₁ := frame_cross L (u - v) 1
  have hI := frame_cross L (u - v) Complex.I
  rw [hz] at h₁ hI
  simp only [cross, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero, zero_sub,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_zero, mul_one] at h₁ hI
  have hre : (u - v).re = 0 := (mul_eq_zero.mp hI.symm).resolve_left (scale_pos hL).ne'
  have him : (u - v).im = 0 := neg_eq_zero.mp ((mul_eq_zero.mp h₁.symm).resolve_left (scale_pos hL).ne')
  apply Complex.ext
  · exact sub_eq_zero.mp hre
  · exact sub_eq_zero.mp him

theorem frame_difference_re (L : ℂ →L[ℝ] ℝ) (a z : ℂ) : (frame L (z - a)).re = L a - L z := by
  rw [frame_re, map_sub]
  ring

def slope (L : ℂ →L[ℝ] ℝ) (a z : ℂ) : ℝ := (frame L (z - a)).im / (frame L (z - a)).re

theorem equal_slope_rays (L : ℂ →L[ℝ] ℝ) (hL : L ≠ 0) (a u v : ℂ)
    (hu : L u < L a) (hv : L v < L a) (he : slope L a u = slope L a v) :
    ∃ k : ℝ, 0 < k ∧ v - a = k • (u - a) := by
  have hU : 0 < (frame L (u - a)).re := by rw [frame_difference_re]; exact sub_pos.mpr hu
  have hV : 0 < (frame L (v - a)).re := by rw [frame_difference_re]; exact sub_pos.mpr hv
  let k := (frame L (v - a)).re / (frame L (u - a)).re
  refine ⟨k, div_pos hV hU, ?_⟩
  apply frame_injective hL
  rw [map_smul, Complex.real_smul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact (div_mul_cancel₀ _ hU.ne').symm
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have hcross := (div_eq_div_iff hU.ne' hV.ne').mp he
    dsimp only [k]
    field_simp [hU.ne']
    nlinarith only [hcross]

theorem slope_lt_orient (L : ℂ →L[ℝ] ℝ) (hL : L ≠ 0) (a u v : ℂ)
    (hu : L u < L a) (hv : L v < L a) (he : slope L a u < slope L a v) : 0 < orient a u v := by
  have hU : 0 < (frame L (u - a)).re := by rw [frame_difference_re]; exact sub_pos.mpr hu
  have hV : 0 < (frame L (v - a)).re := by rw [frame_difference_re]; exact sub_pos.mpr hv
  have hmul := (div_lt_div_iff₀ hU hV).mp he
  have hc : 0 < cross (frame L (u - a)) (frame L (v - a)) := by
    dsimp only [cross]
    nlinarith only [hmul]
  rw [frame_cross] at hc
  have hh : scale L * 0 < scale L * cross (u - a) (v - a) := by simpa only [mul_zero] using hc
  exact (mul_lt_mul_iff_of_pos_left (scale_pos hL)).mp hh

end VeechDichotomy.ExposedRootCoordinates
