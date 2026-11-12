module

public import VeechDichotomy.NormalizedIdealTriangleAngles
public import VeechDichotomy.HyperbolicMobiusAngles
public import VeechDichotomy.HyperbolicAreaSupport
public import VeechDichotomy.NormalizedFullIdealTriangleArea

/-! The actual area-angle identity transports to every actual SL2 image
of a normalized one-ideal triangle. Area invariance and actual derivative
angle preservation prove the formula. Chain rules identify the actual
mapped circle and vertical boundary derivatives used in its finite angles.
No triangle-normalization or transport oracle is introduced. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.MobiusIdealTriangleArea

open LinearGroup NormalizedIdealTriangleCoordinates NormalizedTriangleTangents
open NormalizedIdealTriangleAngles HyperbolicMobiusAngles MeasureTheory
open scoped UpperHalfPlane ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false

def vertex (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) : ℍ :=
  ⟨curve x, by simpa [curve] using height_pos hx₀ hx₁⟩

@[simp] theorem vertex_coe (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    (vertex x hx₀ hx₁ : ℂ) = curve x := rfl

def imageRegion (A : SL2) (a b : ℝ) : Set ℍ := (fun z : ℍ => A • z) '' region a b

def leftImageAngle (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) : ℝ :=
  InnerProductGeometry.angle
    ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) Complex.I)
    ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) (leftTangent x))

def rightImageAngle (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) : ℝ :=
  InnerProductGeometry.angle
    ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) Complex.I)
    ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) (rightTangent x))

theorem leftImageAngle_eq (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    leftImageAngle A x hx₀ hx₁ = leftAngle x :=
  preserves_tangent_angles A (vertex x hx₀ hx₁) Complex.I (leftTangent x)

theorem rightImageAngle_eq (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    rightImageAngle A x hx₀ hx₁ = rightAngle x :=
  preserves_tangent_angles A (vertex x hx₀ hx₁) Complex.I (rightTangent x)

theorem hasDerivAt_image_lower (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    HasDerivAt (fun s : ℝ => extension A (curve s))
      ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) (graphDerivative x)) x := by
  simpa only [Function.comp_def] using!
    (hasFDerivAt_extension_real A (vertex x hx₀ hx₁)).comp_hasDerivAt x (hasDerivAt_curve hx₀ hx₁)

theorem hasDerivAt_image_up (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    HasDerivAt (fun s : ℝ => extension A (upCurve x s))
      ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) Complex.I) 0 := by
  have hpoint : upCurve x 0 = (vertex x hx₀ hx₁ : ℂ) := by simp only [upCurve, vertex_coe, curve, add_zero]
  have hR : HasFDerivAt (extension A) (fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) (upCurve x 0) := by
    rw [hpoint]
    exact hasFDerivAt_extension_real A (vertex x hx₀ hx₁)
  simpa only [Function.comp_def] using! hR.comp_hasDerivAt 0 (hasDerivAt_upCurve x)

theorem leftImageAngle_eq_curve (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    leftImageAngle A x hx₀ hx₁ = InnerProductGeometry.angle
      ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) Complex.I)
      ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) (graphDerivative x)) := by
  rw [preserves_tangent_angles, leftImageAngle_eq]
  exact leftAngle_eq_graph hx₀ hx₁

theorem rightImageAngle_eq_curve (A : SL2) (x : ℝ) (hx₀ : -1 < x) (hx₁ : x < 1) :
    rightImageAngle A x hx₀ hx₁ = InnerProductGeometry.angle
      ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) Complex.I)
      ((fderiv ℝ (extension A) (vertex x hx₀ hx₁ : ℂ)) (-graphDerivative x)) := by
  rw [preserves_tangent_angles, rightImageAngle_eq]
  exact rightAngle_eq_graph hx₀ hx₁

theorem area_imageRegion (A : SL2) (a b : ℝ) : volume (imageRegion A a b) = volume (region a b) :=
  measure_smul (volume : Measure ℍ) A (region a b)

theorem area_formula_images (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    volume (imageRegion A a b) = ENNReal.ofReal (Real.pi - leftImageAngle A a ha (hab.trans_lt hb) -
      rightImageAngle A b (ha.trans_le hab) hb) := by
  rw [area_imageRegion, leftImageAngle_eq, rightImageAngle_eq]
  exact area_formula_angles ha hb hab

theorem area_fullIdeal_image (A : SL2) :
    volume ((fun z : ℍ => A • z) '' NormalizedFullIdealTriangleArea.fullRegion) = ENNReal.ofReal Real.pi :=
  (measure_smul (volume : Measure ℍ) A NormalizedFullIdealTriangleArea.fullRegion).trans
    NormalizedFullIdealTriangleArea.area_full

end VeechDichotomy.MobiusIdealTriangleArea
