module

public import VeechDichotomy.CircularIdealTriangleArea
public import VeechDichotomy.SemicircleTangentAngles

/-! Actual semicircle graph derivatives and oriented tangent vectors for
arbitrary real center and positive radius. Positive scaling identifies
them with the already proved unit-circle tangents, and actual circle
incidence identifies the graph height with a genuine vertex's height. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CircularTriangleTangents

open CircularIdealTriangleArea NormalizedTriangleTangents
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def height (c r x : ℝ) : ℝ := Real.sqrt (r ^ 2 - (x - c) ^ 2)
def curve (c r x : ℝ) : ℂ := (x : ℂ) + (height c r x : ℂ) * Complex.I
def rightwardTangent (c r x : ℝ) : ℂ := ⟨height c r x, c - x⟩
def leftwardTangent (c r x : ℝ) : ℂ := -rightwardTangent c r x
def graphDerivative (c r x : ℝ) : ℂ := 1 + (((c - x) / height c r x : ℝ) : ℂ) * Complex.I

theorem height_rescale {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    height c r x = r * NormalizedIdealTriangleCoordinates.height (coord c r x) := by
  have ht₀ := coord_left hr hx₀
  have ht₁ := coord_right hr hx₁
  have hs : r ^ 2 - (x - c) ^ 2 =
      (r * NormalizedIdealTriangleCoordinates.height (coord c r x)) ^ 2 := by
    rw [mul_pow, NormalizedTriangleTangents.height_sq ht₀ ht₁]
    dsimp only [coord]
    field_simp [hr.ne']
  rw [height, hs]
  exact Real.sqrt_sq (mul_nonneg hr.le (NormalizedTriangleTangents.height_pos ht₀ ht₁).le)

theorem height_pos {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    0 < height c r x := by
  rw [height_rescale hr hx₀ hx₁]
  exact mul_pos hr (NormalizedTriangleTangents.height_pos (coord_left hr hx₀) (coord_right hr hx₁))

theorem height_sq {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    height c r x ^ 2 = r ^ 2 - (x - c) ^ 2 :=
  Real.sq_sqrt (Real.sqrt_pos.mp (height_pos hr hx₀ hx₁)).le

theorem normalized_rightward {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    r • leftTangent (coord c r x) = rightwardTangent c r x := by
  rw [Complex.real_smul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact (height_rescale hr hx₀ hx₁).symm
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    change r * (-coord c r x) = c - x
    dsimp only [coord]
    field_simp [hr.ne']
    ring

theorem normalized_leftward {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    r • rightTangent (coord c r x) = leftwardTangent c r x := by
  rw [rightTangent, smul_neg, normalized_rightward hr hx₀ hx₁]
  rfl

theorem hasDerivAt_height {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    HasDerivAt (height c r) ((c - x) / height c r x) x := by
  have hsq : HasDerivAt (fun y : ℝ => r ^ 2 - (y - c) ^ 2) (-2 * (x - c)) x := by
    simpa using! (hasDerivAt_const x (r ^ 2)).sub (((hasDerivAt_id x).sub_const c).pow 2)
  have h := hsq.sqrt (Real.sqrt_pos.mp (height_pos hr hx₀ hx₁)).ne'
  change HasDerivAt (height c r) ((-2 * (x - c)) / (2 * height c r x)) x at h
  have he : (-2 * (x - c)) / (2 * height c r x) = (c - x) / height c r x := by ring
  rwa [he] at h

theorem hasDerivAt_curve {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    HasDerivAt (curve c r) (graphDerivative c r x) x :=
  (hasDerivAt_id x).ofReal_comp.add (((hasDerivAt_height hr hx₀ hx₁).ofReal_comp).mul_const Complex.I)

theorem scaled_graphDerivative {c r x : ℝ} (hr : 0 < r) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    height c r x • graphDerivative c r x = rightwardTangent c r x := by
  rw [Complex.real_smul]
  have hd : (height c r x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (height_pos hr hx₀ hx₁).ne'
  have hm : (height c r x : ℂ) * (1 + ((c - x : ℝ) : ℂ) / (height c r x : ℂ) * Complex.I) =
      (height c r x : ℂ) + ((c - x : ℝ) : ℂ) * Complex.I := by field_simp [hd]
  simp only [graphDerivative, Complex.ofReal_div]
  rw [hm]
  apply Complex.ext <;> simp [rightwardTangent]

theorem height_eq_im (c r : ℝ) (z : ℍ)
    (hz : Complex.normSq ((z : ℂ) - (c : ℂ)) = r ^ 2) : height c r z.re = z.im := by
  have hs : r ^ 2 - (z.re - c) ^ 2 = z.im ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero] at hz
    linarith
  rw [height, hs, Real.sqrt_sq z.im_pos.le]

theorem curve_eq_point (c r : ℝ) (z : ℍ)
    (hz : Complex.normSq ((z : ℂ) - (c : ℂ)) = r ^ 2) : curve c r z.re = (z : ℂ) := by
  apply Complex.ext <;> simp [curve, height_eq_im c r z hz]

end VeechDichotomy.CircularTriangleTangents
