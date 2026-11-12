module

public import VeechDichotomy.HyperbolicNearestSiteVectors

/-! Exact actual nearest-site normals in physical tangent coordinates.
For two actual equally distant centers the active Klein normal equals
their positive height product times the actual real inner product with
the difference of their actual normalized endpoint vectors. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletSiteNormals

open HyperbolicNearestSiteVectors HyperbolicDirectionVectors HyperbolicBisectorNull
open HyperbolicKleinMap HyperbolicKleinHalfPlanes KleinTangentEquivalence
open scoped UpperHalfPlane

theorem site_difference_re (p q z : ℍ) :
    p.im * q.im * ((site z q).re - (site z p).re) = linear p q / 2 + z.re * leading p q := by
  rw [site_re, site_re]
  dsimp only [linear, leading]
  field_simp [p.im_ne_zero, q.im_ne_zero]
  ring

theorem site_difference_im (p q z : ℍ) (he : dist z p = dist z q) :
    p.im * q.im * ((site z q).im - (site z p).im) = leading p q * z.im := by
  have hz := polynomial_eq_zero p q z he
  simp only [leading, linear, constant, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hz
  rw [site_im, site_im]
  dsimp only [verticalCoefficient, leading]
  field_simp [z.im_ne_zero, p.im_ne_zero, q.im_ne_zero]
  nlinarith only [hz]

theorem normal_im_active (p q z : ℍ) (he : dist z p = dist z q) :
    (leading p q - constant p q) / 2 = (linear p q / 2) * z.re + leading p q * denominator z / 2 := by
  have hz := polynomial_eq_zero p q z he
  dsimp only [denominator]
  nlinarith only [hz]

theorem complex_inner (u v : ℂ) : inner ℝ u v = u.re * v.re + u.im * v.im := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  ring

theorem active_normal_identity (p q z : ℍ) (he : dist z p = dist z q) (u : ℂ) :
    linearPart p q u = p.im * q.im * inner ℝ (site z q - site z p) (forward z u) := by
  rw [complex_inner, Complex.sub_re, Complex.sub_im, forward_re, forward_im]
  have hdistrib : p.im * q.im *
      (((site z q).re - (site z p).re) * (u.re + z.re * u.im) +
        ((site z q).im - (site z p).im) *
          ((-z.re * u.re + (denominator z / 2 - z.re ^ 2) * u.im) / z.im)) =
      (p.im * q.im * ((site z q).re - (site z p).re)) * (u.re + z.re * u.im) +
        (p.im * q.im * ((site z q).im - (site z p).im)) *
          ((-z.re * u.re + (denominator z / 2 - z.re ^ 2) * u.im) / z.im) := by ring
  rw [hdistrib, site_difference_re, site_difference_im p q z he]
  simp only [linearPart, add_apply, smul_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [normal_im_active p q z he]
  field_simp [z.im_ne_zero]
  ring

end VeechDichotomy.DirichletSiteNormals
