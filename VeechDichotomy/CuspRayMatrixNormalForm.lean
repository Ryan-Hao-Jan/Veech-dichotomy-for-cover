module

public import VeechDichotomy.IdealInfinityStabilizers
public import VeechDichotomy.NativeShearMatrices

/-! The exact matrix conversion from an upper cusp period to the
contracted lower unipotent for a ray whose transformed lower-right
entry vanishes. Determinant one proves the parameter is nonzero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CuspRayMatrixNormalForm

open LinearGroup IdealInfinityStabilizers NativeShearMatrices

set_option backward.isDefEq.respectTransparency false

theorem lower_left_ne_zero (C : SL2) (hd : C 1 1 = 0) : C 1 0 ≠ 0 := by
  intro hc
  have he := C.property
  simp only [Matrix.det_fin_two, hd, hc, mul_zero, sub_self] at he
  exact zero_ne_one he

theorem conjugate_upper (C : SL2) (hd : C 1 1 = 0) (τ : ℝ) :
    C⁻¹ * upper τ * C = lower (-(C 1 0 ^ 2) * τ) := by
  have hdet := C.property
  rw [Matrix.det_fin_two, hd, mul_zero, zero_sub] at hdet
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, upper, lower, hd] <;>
    nlinarith only [hdet]

theorem parameter_ne_zero (C : SL2) (hd : C 1 1 = 0) {τ : ℝ} (hτ : τ ≠ 0) : -(C 1 0 ^ 2) * τ ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (lower_left_ne_zero C hd))) hτ

end VeechDichotomy.CuspRayMatrixNormalForm
