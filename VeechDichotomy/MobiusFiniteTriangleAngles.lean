module

public import VeechDichotomy.FiniteTriangleBoundaryDerivatives
public import VeechDichotomy.CircularGeodesicArcs

/-! The finite-triangle area-angle identity after any actual SL2 map.
Every angle uses the actual real derivative at its genuine vertex.
Actual conformality and chain rules identify these with actual mapped
boundary-curve derivatives and transport the proved area identity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.MobiusFiniteTriangleAngles

open LinearGroup MeasureTheory HyperbolicTriangles MobiusIdealTriangleArea HyperbolicMobiusAngles
open NormalizedTriangleTangents NormalizedFiniteTriangleArea NormalizedFiniteTriangleAngles
open FiniteTriangleBoundaryDerivatives
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

def lowerImageAngle (A : SL2) (a : ℝ) (ha₀ : -1 < a) (ha₁ : a < 1) : ℝ :=
  InnerProductGeometry.angle
    ((fderiv ℝ (extension A) (vertex a ha₀ ha₁ : ℂ)) Complex.I)
    ((fderiv ℝ (extension A) (vertex a ha₀ ha₁ : ℂ)) (leftTangent a))

def upperImageAngle (A : SL2) (a b : ℝ) (p : ℍ) : ℝ :=
  InnerProductGeometry.angle ((fderiv ℝ (extension A) (p : ℂ)) (-Complex.I))
    ((fderiv ℝ (extension A) (p : ℂ))
      (CircularTriangleTangents.rightwardTangent (center a b p) (radius a b p) a))

def rightImageAngle (A : SL2) (a b : ℝ) (p : ℍ) (hb₀ : -1 < b) (hb₁ : b < 1) : ℝ :=
  InnerProductGeometry.angle
    ((fderiv ℝ (extension A) (vertex b hb₀ hb₁ : ℂ)) (rightTangent b))
    ((fderiv ℝ (extension A) (vertex b hb₀ hb₁ : ℂ))
      (CircularTriangleTangents.leftwardTangent (center a b p) (radius a b p) b))

theorem lowerImageAngle_eq (A : SL2) (a : ℝ) (ha₀ : -1 < a) (ha₁ : a < 1) :
    lowerImageAngle A a ha₀ ha₁ = lowerAngle a :=
  preserves_tangent_angles A (vertex a ha₀ ha₁) _ _

theorem upperImageAngle_eq (A : SL2) (a b : ℝ) (p : ℍ) : upperImageAngle A a b p = upperAngle a b p :=
  preserves_tangent_angles A p _ _

theorem rightImageAngle_eq (A : SL2) (a b : ℝ) (p : ℍ) (hb₀ : -1 < b) (hb₁ : b < 1) :
    rightImageAngle A a b p hb₀ hb₁ = rightAngle a b p :=
  preserves_tangent_angles A (vertex b hb₀ hb₁) _ _

theorem hasDerivAt_mapped (A : SL2) (z : ℍ) (f : ℝ → ℂ) (v : ℂ)
    (hf : HasDerivAt f v 0) (hz : f 0 = (z : ℂ)) :
    HasDerivAt (fun s : ℝ => extension A (f s)) ((fderiv ℝ (extension A) (z : ℂ)) v) 0 := by
  have hF : HasFDerivAt (extension A) (fderiv ℝ (extension A) (z : ℂ)) (f 0) := by
    rw [hz]
    exact hasFDerivAt_extension_real A z
  simpa only [Function.comp_def] using! hF.comp_hasDerivAt 0 hf

theorem mapped_curve_angle (A : SL2) (z : ℍ) (f g : ℝ → ℂ) (v w : ℂ)
    (hf : HasDerivAt f v 0) (hg : HasDerivAt g w 0) (hzf : f 0 = (z : ℂ)) (hzg : g 0 = (z : ℂ)) :
    InnerProductGeometry.angle (deriv (fun s : ℝ => extension A (f s)) 0)
      (deriv (fun s : ℝ => extension A (g s)) 0) = InnerProductGeometry.angle v w := by
  rw [(hasDerivAt_mapped A z f v hf hzf).deriv, (hasDerivAt_mapped A z g w hg hzg).deriv]
  exact preserves_tangent_angles A z v w

theorem lowerImageAngle_eq_derivatives (A : SL2) {a : ℝ} (ha₀ : -1 < a) (ha₁ : a < 1) :
    lowerImageAngle A a ha₀ ha₁ = InnerProductGeometry.angle
      (deriv (fun s : ℝ => extension A (up (vertex a ha₀ ha₁) s)) 0)
      (deriv (fun s : ℝ => extension A (shiftRight NormalizedTriangleTangents.curve a s)) 0) := by
  rw [lowerImageAngle_eq, mapped_curve_angle A (vertex a ha₀ ha₁) _ _ _ _ (hasDerivAt_up _)
    (hasDerivAt_shiftRight (hasDerivAt_curve ha₀ ha₁)) (by simp [up]) (by simp [shiftRight, vertex_coe])]
  exact lowerAngle_eq_graph ha₀ ha₁

theorem upperImageAngle_eq_derivatives (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : upperImageAngle A a b p = InnerProductGeometry.angle
      (deriv (fun s : ℝ => extension A (down p s)) 0)
      (deriv (fun s : ℝ => extension A
        (shiftRight (CircularTriangleTangents.curve (center a b p) (radius a b p)) a s)) 0) := by
  have hcurve := CircularTriangleTangents.hasDerivAt_curve (radius_pos a b p) (left_diameter p hpre)
    (hab.trans (right_diameter ha hb hab p hpre))
  have hsource : shiftRight (CircularTriangleTangents.curve (center a b p) (radius a b p)) a 0 = (p : ℂ) := by
    simpa only [shiftRight, add_zero] using upper_curve_left p hpre
  rw [upperImageAngle_eq, mapped_curve_angle A p _ _ _ _ (hasDerivAt_down p)
    (hasDerivAt_shiftRight hcurve) (by simp [down]) hsource]
  exact upperAngle_eq_graph ha hb hab p hpre

theorem rightImageAngle_eq_derivatives (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : rightImageAngle A a b p (ha.trans hab) hb = InnerProductGeometry.angle
      (deriv (fun s : ℝ => extension A (shiftLeft NormalizedTriangleTangents.curve b s)) 0)
      (deriv (fun s : ℝ => extension A
        (shiftLeft (CircularTriangleTangents.curve (center a b p) (radius a b p)) b s)) 0) := by
  have hcurve := CircularTriangleTangents.hasDerivAt_curve (radius_pos a b p)
    ((left_diameter p hpre).trans hab) (right_diameter ha hb hab p hpre)
  have hsource : shiftLeft (CircularTriangleTangents.curve (center a b p) (radius a b p)) b 0 =
      (vertex b (ha.trans hab) hb : ℂ) := by
    simpa only [shiftLeft, sub_zero] using upper_curve_right ha hb hab p hpre
  rw [rightImageAngle_eq, mapped_curve_angle A (vertex b (ha.trans hab) hb) _ _ _ _
    (hasDerivAt_shiftLeft (hasDerivAt_curve (ha.trans hab) hb)) (hasDerivAt_shiftLeft hcurve)
    (by simp [shiftLeft, vertex_coe]) hsource]
  exact rightAngle_eq_graph ha hb hab p hpre

theorem real_area_angles (A : SL2) {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    (volume (triangle (A • vertex a ha (hab.trans hb)) (A • vertex b (ha.trans hab) hb) (A • p))).toReal =
      Real.pi - (lowerImageAngle A a ha (hab.trans hb) + rightImageAngle A a b p (ha.trans hab) hb +
        upperImageAngle A a b p) := by
  rw [lowerImageAngle_eq, rightImageAngle_eq, upperImageAngle_eq, ← image_triangle_smul]
  have hm : volume ((fun z : ℍ => A • z) '' triangle (vertex a ha (hab.trans hb))
      (vertex b (ha.trans hab) hb) p) =
      volume (triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p) :=
    measure_smul (volume : Measure ℍ) A _
  rw [hm]
  exact NormalizedFiniteTriangleAngles.real_area_angles ha hb hab p hpre hp

end VeechDichotomy.MobiusFiniteTriangleAngles
