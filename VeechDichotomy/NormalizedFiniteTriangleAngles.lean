module

public import VeechDichotomy.NormalizedFiniteTriangleParameters

/-! The three actual tangent angles of a normalized finite hyperbolic
triangle satisfy area = pi minus their sum. The right angle is between
the two actual left-pointing circle tangents; its orientation follows
from the proved strict upper-circle parameter ordering. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedFiniteTriangleAngles

open Set MeasureTheory HyperbolicTriangles MobiusIdealTriangleArea
open NormalizedTriangleTangents NormalizedFiniteTriangleArea NormalizedFiniteTriangleParameters
open scoped UpperHalfPlane ENNReal

def lowerAngle (a : ℝ) : ℝ := InnerProductGeometry.angle (Complex.I : ℂ) (leftTangent a)

def upperAngle (a b : ℝ) (p : ℍ) : ℝ := InnerProductGeometry.angle (-Complex.I : ℂ)
  (CircularTriangleTangents.rightwardTangent (center a b p) (radius a b p) a)

def rightAngle (a b : ℝ) (p : ℍ) : ℝ := InnerProductGeometry.angle (rightTangent b)
  (CircularTriangleTangents.leftwardTangent (center a b p) (radius a b p) b)

theorem lowerAngle_formula {a : ℝ} (ha₀ : -1 < a) (ha₁ : a < 1) :
    lowerAngle a = Real.pi / 2 + Real.arcsin a :=
  NormalizedIdealTriangleAngles.leftAngle_formula ha₀ ha₁

theorem upperAngle_formula {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) :
    upperAngle a b p = Real.pi / 2 - Real.arcsin (upperCoord a b p a) := by
  rw [upperAngle, ← CircularTriangleTangents.normalized_rightward (radius_pos a b p)
    (left_diameter p hpre) (hab.trans (right_diameter ha hb hab p hpre)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (radius_pos a b p),
    InnerProductGeometry.angle_neg_left]
  have ht := upper_left_bounds ha hb hab p hpre
  change Real.pi - NormalizedIdealTriangleAngles.leftAngle (upperCoord a b p a) = _
  rw [NormalizedIdealTriangleAngles.leftAngle_formula ht.1 ht.2]
  ring

theorem rightAngle_formula {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    rightAngle a b p = Real.arcsin (upperCoord a b p b) - Real.arcsin b := by
  rw [rightAngle, ← CircularTriangleTangents.normalized_leftward (radius_pos a b p)
    ((left_diameter p hpre).trans hab) (right_diameter ha hb hab p hpre),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (radius_pos a b p)]
  have ht := upper_right_bounds ha hb hab p hpre
  exact SemicircleTangentAngles.right_angle_of_le (ha.trans hab) hb ht.1 ht.2
    (upper_right_gt ha hb hab p hpre hp).le

theorem real_area_angles {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    (volume (triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p)).toReal =
      Real.pi - (lowerAngle a + rightAngle a b p + upperAngle a b p) := by
  rw [NormalizedFiniteTriangleArea.real_area_formula ha hb hab p hpre hp,
    lowerAngle_formula ha (hab.trans hb), upperAngle_formula ha hb hab p hpre,
    rightAngle_formula ha hb hab p hpre hp]
  change _ = Real.pi - (Real.pi / 2 + Real.arcsin a +
    (Real.arcsin (CircularIdealTriangleArea.coord (center a b p) (radius a b p) b) - Real.arcsin b) +
    (Real.pi / 2 - Real.arcsin (CircularIdealTriangleArea.coord (center a b p) (radius a b p) a)))
  ring

theorem angle_sum_le_pi {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) :
    lowerAngle a + rightAngle a b p + upperAngle a b p ≤ Real.pi := by
  have hn := ENNReal.toReal_nonneg (a := volume
    (triangle (vertex a ha (hab.trans hb)) (vertex b (ha.trans hab) hb) p))
  rw [real_area_angles ha hb hab p hpre hp] at hn
  linarith

theorem lowerAngle_pos {a : ℝ} (ha₀ : -1 < a) (ha₁ : a < 1) : 0 < lowerAngle a :=
  (NormalizedIdealTriangleAngles.leftAngle_range ha₀ ha₁).1

theorem upperAngle_pos {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) : 0 < upperAngle a b p := by
  rw [upperAngle_formula ha hb hab p hpre]
  have h := Real.arcsin_lt_pi_div_two.mpr (upper_left_bounds ha hb hab p hpre).2
  linarith

theorem rightAngle_pos {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a < b)
    (p : ℍ) (hpre : p.re = a) (hp : 1 < Complex.normSq (p : ℂ)) : 0 < rightAngle a b p := by
  rw [rightAngle_formula ha hb hab p hpre hp]
  apply sub_pos.mpr
  have ht := upper_right_bounds ha hb hab p hpre
  exact Real.strictMonoOn_arcsin ⟨(ha.trans hab).le, hb.le⟩ ⟨ht.1.le, ht.2.le⟩
    (upper_right_gt ha hb hab p hpre hp)

end VeechDichotomy.NormalizedFiniteTriangleAngles
