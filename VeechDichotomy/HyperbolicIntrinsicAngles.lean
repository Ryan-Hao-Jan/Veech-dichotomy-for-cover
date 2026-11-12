module

public import VeechDichotomy.HyperbolicDirectionVectors

/-! An actual endpoint-vector corner angle with a proved intrinsic
hyperbolic cosine law. Actual distance invariance then proves SL2
invariance of this fixed angle function; no choice of normal form
enters its definition. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicIntrinsicAngles

open LinearGroup HyperbolicDirectionVectors
open scoped UpperHalfPlane

def angleAt (a b c : ℍ) : ℝ := InnerProductGeometry.angle (direction a b) (direction a c)

theorem cosine_law (a b c : ℍ) : angleAt a b c = Real.arccos
    ((Real.cosh (dist a b) * Real.cosh (dist a c) - Real.cosh (dist b c)) /
      (Real.sinh (dist a b) * Real.sinh (dist a c))) := by
  rw [angleAt, InnerProductGeometry.angle, inner_formula, norm_formula, norm_formula]
  congr 1
  have hfactor : (b.im * Real.sinh (dist a b)) * (c.im * Real.sinh (dist a c)) =
      (b.im * c.im) * (Real.sinh (dist a b) * Real.sinh (dist a c)) := by ring
  rw [hfactor]
  exact mul_div_mul_left _ _ (mul_ne_zero b.im_ne_zero c.im_ne_zero)

theorem angleAt_smul (A : SL2) (a b c : ℍ) : angleAt (A • a) (A • b) (A • c) = angleAt a b c := by
  rw [cosine_law, cosine_law, dist_smul, dist_smul, dist_smul]

theorem angleAt_comm (a b c : ℍ) : angleAt a b c = angleAt a c b :=
  InnerProductGeometry.angle_comm _ _

theorem angleAt_nonneg (a b c : ℍ) : 0 ≤ angleAt a b c := InnerProductGeometry.angle_nonneg _ _
theorem angleAt_le_pi (a b c : ℍ) : angleAt a b c ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _

def angleSum (a b c : ℍ) : ℝ := angleAt a b c + angleAt b a c + angleAt c a b

theorem angleSum_smul (A : SL2) (a b c : ℍ) : angleSum (A • a) (A • b) (A • c) = angleSum a b c := by
  simp only [angleSum, angleAt_smul]

theorem angleSum_swap (a b c : ℍ) : angleSum a b c = angleSum b a c := by
  unfold angleSum
  rw [angleAt_comm c a b]
  ring

theorem angleSum_rotate (a b c : ℍ) : angleSum a b c = angleSum b c a := by
  unfold angleSum
  rw [angleAt_comm b a c, angleAt_comm c a b]
  ring

end VeechDichotomy.HyperbolicIntrinsicAngles
