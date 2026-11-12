module

public import VeechDichotomy.NormalizedTriangleTangents
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-! Actual tangent angles and the area-angle identity for the normalized
one-ideal hyperbolic triangle. The two finite angles are the genuine
Euclidean angles between its upward vertical and proved circle tangent
directions. Their formulas follow from actual real inner products and
unit tangent norms, and the actual hyperbolic area integral gives
area = pi - leftAngle - rightAngle. No area-angle oracle is introduced. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedIdealTriangleAngles

open NormalizedIdealTriangleCoordinates NormalizedTriangleTangents MeasureTheory
open scoped UpperHalfPlane RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false

def leftAngle (x : ℝ) : ℝ := InnerProductGeometry.angle (Complex.I : ℂ) (leftTangent x)
def rightAngle (x : ℝ) : ℝ := InnerProductGeometry.angle (Complex.I : ℂ) (rightTangent x)

theorem inner_leftTangent (x : ℝ) : inner ℝ (Complex.I : ℂ) (leftTangent x) = -x := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, leftTangent]

theorem leftAngle_formula {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    leftAngle x = Real.pi / 2 + Real.arcsin x := by
  rw [leftAngle, InnerProductGeometry.angle, inner_leftTangent, Complex.norm_I,
    leftTangent_norm hx₀ hx₁, one_mul, div_one, Real.arccos_neg, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

theorem rightAngle_formula {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    rightAngle x = Real.pi / 2 - Real.arcsin x := by
  rw [rightAngle, rightTangent, InnerProductGeometry.angle_neg_right]
  change Real.pi - leftAngle x = _
  rw [leftAngle_formula hx₀ hx₁]
  ring

theorem leftAngle_eq_graph {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    leftAngle x = InnerProductGeometry.angle (Complex.I : ℂ) (graphDerivative x) := by
  rw [leftAngle, ← scaled_graphDerivative hx₀ hx₁]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ (height_pos hx₀ hx₁)

theorem rightAngle_eq_graph {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) :
    rightAngle x = InnerProductGeometry.angle (Complex.I : ℂ) (-graphDerivative x) := by
  rw [rightAngle, rightTangent, ← scaled_graphDerivative hx₀ hx₁, ← smul_neg]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ (height_pos hx₀ hx₁)

theorem leftAngle_range {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) : 0 < leftAngle x ∧ leftAngle x < Real.pi := by
  rw [leftAngle_formula hx₀ hx₁]
  have h₀ := Real.neg_pi_div_two_lt_arcsin.mpr hx₀
  have h₁ := Real.arcsin_lt_pi_div_two.mpr hx₁
  constructor <;> linarith

theorem rightAngle_range {x : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) : 0 < rightAngle x ∧ rightAngle x < Real.pi := by
  rw [rightAngle_formula hx₀ hx₁]
  have h₀ := Real.neg_pi_div_two_lt_arcsin.mpr hx₀
  have h₁ := Real.arcsin_lt_pi_div_two.mpr hx₁
  constructor <;> linarith

theorem area_formula_angles {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    volume (region a b) = ENNReal.ofReal (Real.pi - leftAngle a - rightAngle b) := by
  rw [NormalizedIdealTriangleArea.area_formula ha hb hab,
    leftAngle_formula ha (hab.trans_lt hb), rightAngle_formula (ha.trans_le hab) hb]
  congr 1
  ring

end VeechDichotomy.NormalizedIdealTriangleAngles
