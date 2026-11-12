module

public import VeechDichotomy.DirichletTileCenters

/-! Actual normalized endpoint vectors for nearest-center geometry.
Their norm is sinh of the actual hyperbolic distance. A direct reciprocal
height identity proves that equal vectors on one actual distance circle
come from the same actual upper-half-plane point. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicNearestSiteVectors

open HyperbolicDirectionVectors
open scoped UpperHalfPlane

def site (z q : ℍ) : ℂ := (1 / q.im : ℝ) • direction z q

theorem site_re (z q : ℍ) : (site z q).re = (q.re - z.re) / q.im := by
  rw [site, Complex.real_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change (1 / q.im) * (q.re - z.re) = (q.re - z.re) / q.im
  ring

theorem site_im (z q : ℍ) : (site z q).im = verticalCoefficient z q / q.im := by
  rw [site, Complex.real_smul]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  change (1 / q.im) * verticalCoefficient z q = verticalCoefficient z q / q.im
  ring

theorem site_norm (z q : ℍ) : ‖site z q‖ = Real.sinh (dist z q) := by
  rw [site, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one q.im_pos), norm_formula]
  field_simp [q.im_ne_zero]

theorem cosh_sub_site_im (z q : ℍ) : Real.cosh (dist z q) - (site z q).im = z.im / q.im := by
  rw [UpperHalfPlane.cosh_dist', site_im]
  dsimp only [verticalCoefficient]
  field_simp [z.im_ne_zero, q.im_ne_zero]
  ring

theorem site_injective_on_circle (z q r : ℍ) (hd : dist z q = dist z r) (he : site z q = site z r) : q = r := by
  have hq := cosh_sub_site_im z q
  have hr := cosh_sub_site_im z r
  have him := congrArg Complex.im he
  have hc := congrArg Real.cosh hd
  have hrecip : z.im / q.im = z.im / r.im := by linarith only [hq, hr, him, hc]
  have hprod := (div_eq_div_iff q.im_ne_zero r.im_ne_zero).mp hrecip
  have hzero : z.im * (r.im - q.im) = 0 := by nlinarith only [hprod]
  have hi : q.im = r.im := (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left z.im_ne_zero)).symm
  have hre := congrArg Complex.re he
  rw [site_re, site_re, hi] at hre
  have hmul := congrArg (fun t : ℝ => t * r.im) hre
  simp only [div_mul_cancel₀ _ r.im_ne_zero] at hmul
  apply UpperHalfPlane.ext_re_im _ hi
  linarith only [hmul]

end VeechDichotomy.HyperbolicNearestSiteVectors
