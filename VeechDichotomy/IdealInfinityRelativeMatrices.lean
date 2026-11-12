module

public import VeechDichotomy.SL2BottomRowEndpoints
public import VeechDichotomy.IdealInfinityStabilizers

/-! Two distinct actual orbit centers with the same bottom-row ideal
endpoint give an actual nonzero upper unipotent in the group. Their
relative matrix fixes infinity and genuinely moves an actual point. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.IdealInfinityRelativeMatrices

open LinearGroup DirichletIdealRadialPoints IdealInfinityStabilizers
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem relative_lower_left (B C : SL2) (he : SL2BottomRowEndpoints.endpoint B = SL2BottomRowEndpoints.endpoint C) :
    (B * C⁻¹) 1 0 = 0 := by
  calc
    _ = B 1 0 * C 1 1 - B 1 1 * C 1 0 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    _ = 0 := SL2BottomRowEndpoints.rows_proportional B C he

theorem scalar_matrix_fixes (B : SL2) (hc : B 1 0 = 0) (hb : B 0 1 = 0)
    (hd : B 1 1 = B 0 0) (han : B 0 0 ≠ 0) (z : ℍ) : B • z = z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, hc, hb, hd,
    Complex.ofReal_zero, zero_mul, zero_add, add_zero]
  have hanc : (B 0 0 : ℂ) ≠ 0 := by exact_mod_cast han
  field_simp [hanc]

theorem exists_upper_of_equal_endpoints (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (γ δ : Γ) (he : SL2BottomRowEndpoints.endpoint γ = SL2BottomRowEndpoints.endpoint δ)
    (hne : γ • p ≠ δ • p) : ∃ s : ℝ, s ≠ 0 ∧ upper s ∈ Γ := by
  let η : Γ := γ * δ⁻¹
  have hc : (η : SL2) 1 0 = 0 := relative_lower_left γ δ he
  obtain ⟨hs, hd⟩ := diagonal_square Γ p hI η hc
  have han : (η : SL2) 0 0 ≠ 0 := by intro hz; rw [hz] at hs; norm_num at hs
  have hmove : η • (δ • p) = γ • p := by dsimp only [η]; rw [mul_smul, inv_smul_smul]
  have hb : (η : SL2) 0 1 ≠ 0 := by
    intro hz
    have hfix := scalar_matrix_fixes η hc hz hd han (δ • p)
    change η • (δ • p) = δ • p at hfix
    rw [hmove] at hfix
    exact hne hfix
  exact exists_nonzero_upper Γ p hI η hc hb

end VeechDichotomy.IdealInfinityRelativeMatrices
