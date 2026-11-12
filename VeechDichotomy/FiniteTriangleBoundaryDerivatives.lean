module

public import VeechDichotomy.NormalizedFiniteTriangleAngles

/-! The finite triangle's corner angles are angles of actual derivatives
of its oriented boundary curves. Actual circle graphs pass through the
literal vertices; parameter shifts orient each circle towards its opposite
vertex, and vertical curves have the actual upward/downward derivatives. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FiniteTriangleBoundaryDerivatives

open NormalizedFiniteTriangleArea NormalizedFiniteTriangleParameters
open NormalizedFiniteTriangleAngles NormalizedTriangleTangents MobiusIdealTriangleArea
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def shiftRight (f : ℝ → ℂ) (x : ℝ) (s : ℝ) : ℂ := f (x + s)
def shiftLeft (f : ℝ → ℂ) (x : ℝ) (s : ℝ) : ℂ := f (x - s)
def up (z : ℍ) (s : ℝ) : ℂ := (z : ℂ) + (s : ℂ) * Complex.I
def down (z : ℍ) (s : ℝ) : ℂ := (z : ℂ) - (s : ℂ) * Complex.I

theorem hasDerivAt_shiftRight {f : ℝ → ℂ} {x : ℝ} {v : ℂ} (hf : HasDerivAt f v x) :
    HasDerivAt (shiftRight f x) v 0 := by
  have hf' : HasDerivAt f v (x + 0) := by simpa using hf
  have h := hf'.scomp 0 ((hasDerivAt_const (0 : ℝ) x).add (hasDerivAt_id 0))
  simpa only [shiftRight, zero_add, one_smul] using! h

theorem hasDerivAt_shiftLeft {f : ℝ → ℂ} {x : ℝ} {v : ℂ} (hf : HasDerivAt f v x) :
    HasDerivAt (shiftLeft f x) (-v) 0 := by
  have hf' : HasDerivAt f v (x - 0) := by simpa using hf
  have h := hf'.scomp 0 ((hasDerivAt_const (0 : ℝ) x).sub (hasDerivAt_id 0))
  simpa only [shiftLeft, zero_sub, neg_smul, one_smul] using! h

theorem hasDerivAt_up (z : ℍ) : HasDerivAt (up z) Complex.I 0 := by
  simpa only [up, zero_add, Complex.ofReal_one, one_mul] using!
    (hasDerivAt_const (0 : ℝ) (z : ℂ)).add ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I)

theorem hasDerivAt_down (z : ℍ) : HasDerivAt (down z) (-Complex.I) 0 := by
  simpa only [down, zero_sub, Complex.ofReal_one, one_mul] using!
    (hasDerivAt_const (0 : ℝ) (z : ℂ)).sub ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I)

theorem upper_curve_left {a b : ℝ} (p : ℍ) (hpre : p.re = a) :
    CircularTriangleTangents.curve (center a b p) (radius a b p) a = (p : ℂ) := by
  have h := CircularTriangleTangents.curve_eq_point (center a b p) (radius a b p) p (circle_incidence a b p)
  rwa [hpre] at h

theorem upper_curve_right {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) :
    CircularTriangleTangents.curve (center a b p) (radius a b p) b =
      (vertex b (ha.trans hab) hb : ℂ) := by
  have h := CircularTriangleTangents.curve_eq_point (center a b p) (radius a b p)
    (vertex b (ha.trans hab) hb) (right_circle_incidence ha hb hab p hpre)
  simpa [vertex, NormalizedTriangleTangents.curve] using h

theorem lowerAngle_eq_graph {a : ℝ} (ha₀ : -1 < a) (ha₁ : a < 1) :
    lowerAngle a = InnerProductGeometry.angle (Complex.I : ℂ) (graphDerivative a) :=
  NormalizedIdealTriangleAngles.leftAngle_eq_graph ha₀ ha₁

theorem upperAngle_eq_graph {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : upperAngle a b p = InnerProductGeometry.angle (-Complex.I : ℂ)
      (CircularTriangleTangents.graphDerivative (center a b p) (radius a b p) a) := by
  rw [upperAngle, ← CircularTriangleTangents.scaled_graphDerivative (radius_pos a b p)
    (left_diameter p hpre) (hab.trans (right_diameter ha hb hab p hpre))]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _
    (CircularTriangleTangents.height_pos (radius_pos a b p) (left_diameter p hpre)
      (hab.trans (right_diameter ha hb hab p hpre)))

theorem rightAngle_eq_graph {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : rightAngle a b p = InnerProductGeometry.angle (-graphDerivative b)
      (-CircularTriangleTangents.graphDerivative (center a b p) (radius a b p) b) := by
  have hl : rightTangent b = NormalizedIdealTriangleCoordinates.height b • (-graphDerivative b) := by
    rw [rightTangent, smul_neg, scaled_graphDerivative (ha.trans hab) hb]
  have hu : CircularTriangleTangents.leftwardTangent (center a b p) (radius a b p) b =
      CircularTriangleTangents.height (center a b p) (radius a b p) b •
        (-CircularTriangleTangents.graphDerivative (center a b p) (radius a b p) b) := by
    rw [CircularTriangleTangents.leftwardTangent, smul_neg,
      CircularTriangleTangents.scaled_graphDerivative (radius_pos a b p)
        ((left_diameter p hpre).trans hab) (right_diameter ha hb hab p hpre)]
  rw [rightAngle, hl, hu,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (NormalizedTriangleTangents.height_pos (ha.trans hab) hb),
    InnerProductGeometry.angle_smul_right_of_pos _ _
      (CircularTriangleTangents.height_pos (radius_pos a b p)
        ((left_diameter p hpre).trans hab) (right_diameter ha hb hab p hpre))]

theorem lowerAngle_eq_derivatives {a : ℝ} (ha₀ : -1 < a) (ha₁ : a < 1) :
    lowerAngle a = InnerProductGeometry.angle (deriv (up (vertex a ha₀ ha₁)) 0)
      (deriv (shiftRight NormalizedTriangleTangents.curve a) 0) := by
  rw [(hasDerivAt_up _).deriv, (hasDerivAt_shiftRight (hasDerivAt_curve ha₀ ha₁)).deriv]
  exact lowerAngle_eq_graph ha₀ ha₁

theorem upperAngle_eq_derivatives {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : upperAngle a b p = InnerProductGeometry.angle (deriv (down p) 0)
      (deriv (shiftRight (CircularTriangleTangents.curve (center a b p) (radius a b p)) a) 0) := by
  rw [(hasDerivAt_down _).deriv, (hasDerivAt_shiftRight
    (CircularTriangleTangents.hasDerivAt_curve (radius_pos a b p) (left_diameter p hpre)
      (hab.trans (right_diameter ha hb hab p hpre)))).deriv]
  exact upperAngle_eq_graph ha hb hab p hpre

theorem rightAngle_eq_derivatives {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : rightAngle a b p = InnerProductGeometry.angle
      (deriv (shiftLeft NormalizedTriangleTangents.curve b) 0)
      (deriv (shiftLeft (CircularTriangleTangents.curve (center a b p) (radius a b p)) b) 0) := by
  rw [(hasDerivAt_shiftLeft (hasDerivAt_curve (ha.trans hab) hb)).deriv,
    (hasDerivAt_shiftLeft (CircularTriangleTangents.hasDerivAt_curve (radius_pos a b p)
      ((left_diameter p hpre).trans hab) (right_diameter ha hb hab p hpre))).deriv]
  exact rightAngle_eq_graph ha hb hab p hpre

end VeechDichotomy.FiniteTriangleBoundaryDerivatives
