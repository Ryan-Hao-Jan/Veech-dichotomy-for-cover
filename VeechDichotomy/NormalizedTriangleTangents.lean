module

public import VeechDichotomy.NormalizedIdealTriangleArea
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual boundary curves and tangent directions of the normalized
one-ideal triangle. The unit semicircle graph has a proved derivative;
positive height rescales it to the actual unit tangent pointing right,
whose negative points left. The upward vertical boundary derivative is i.
No angle or tangent-vector identification is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedTriangleTangents

open NormalizedIdealTriangleCoordinates Set

set_option backward.isDefEq.respectTransparency false

def curve (x : ℝ) : ℂ := (x : ℂ) + (height x : ℂ) * Complex.I
def upCurve (x s : ℝ) : ℂ := (x : ℂ) + ((height x + s : ℝ) : ℂ) * Complex.I
def leftTangent (x : ℝ) : ℂ := ⟨height x, -x⟩
def rightTangent (x : ℝ) : ℂ := -leftTangent x
def graphDerivative (x : ℝ) : ℂ := 1 + (((-x / height x : ℝ)) : ℂ) * Complex.I

theorem height_pos {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) : 0 < height x :=
  ArcsineAreaIntegral.height_pos hx₀ hx₁ ⟨le_rfl, le_rfl⟩

theorem height_sq {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) : height x ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (Real.sqrt_pos.mp (height_pos hx₀ hx₁)).le

theorem hasDerivAt_height {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    HasDerivAt height (-x / height x) x := by
  have hsq : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa using! (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
  have h := hsq.sqrt (Real.sqrt_pos.mp (height_pos hx₀ hx₁)).ne'
  change HasDerivAt height ((-2 * x) / (2 * height x)) x at h
  have hcoef : (-2 * x) / (2 * height x) = -x / height x := by ring
  rwa [hcoef] at h

theorem hasDerivAt_curve {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    HasDerivAt curve (graphDerivative x) x := by
  exact (hasDerivAt_id x).ofReal_comp.add (((hasDerivAt_height hx₀ hx₁).ofReal_comp).mul_const Complex.I)

theorem hasDerivAt_upCurve (x : ℝ) : HasDerivAt (upCurve x) Complex.I 0 := by
  have h := (hasDerivAt_const (0 : ℝ) (x : ℂ)).add
    ((((hasDerivAt_const (0 : ℝ) (height x)).add (hasDerivAt_id 0)).ofReal_comp).mul_const Complex.I)
  simpa only [upCurve, zero_add, Complex.ofReal_one, one_mul] using! h

theorem scaled_graphDerivative {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    (height x : ℝ) • graphDerivative x = leftTangent x := by
  rw [Complex.real_smul]
  have heq : graphDerivative x = 1 - (x : ℂ) / (height x : ℂ) * Complex.I := by
    simp only [graphDerivative, Complex.ofReal_div, Complex.ofReal_neg]
    ring
  rw [heq]
  have hm : (height x : ℂ) * (1 - (x : ℂ) / (height x : ℂ) * Complex.I) =
      (height x : ℂ) - (x : ℂ) * Complex.I := by
    field_simp [Complex.ofReal_ne_zero.mpr (height_pos hx₀ hx₁).ne']
  rw [hm]
  apply Complex.ext <;> simp [leftTangent]

theorem leftTangent_norm {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) : ‖leftTangent x‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Complex.sq_norm]
  simp only [leftTangent, Complex.normSq_apply]
  nlinarith only [height_sq hx₀ hx₁]

theorem rightTangent_norm {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) : ‖rightTangent x‖ = 1 := by
  rw [rightTangent, norm_neg]
  exact leftTangent_norm hx₀ hx₁

end VeechDichotomy.NormalizedTriangleTangents
