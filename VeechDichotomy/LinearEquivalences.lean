module

public import VeechDichotomy.NativeVeech

/-! The actual SL2 action as continuous real-linear plane equivalences,
with multiplication, inverse, determinant and parameter continuity proved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.LinearEquivalences

open MNEC.LatticeTorus NativeVeech LinearGroup

def planeEquiv (A : SL2) : Plane ≃L[ℝ] Plane where
  toFun := linear A
  invFun := linear A⁻¹
  left_inv p := by
    have h := congrArg (fun f : Plane →L[ℝ] Plane => f p) (linear_mul A⁻¹ A)
    simpa only [inv_mul_cancel, linear_one, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply] using h.symm
  right_inv p := by
    have h := congrArg (fun f : Plane →L[ℝ] Plane => f p) (linear_mul A A⁻¹)
    simpa only [mul_inv_cancel, linear_one, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply] using h.symm
  map_add' := (linear A).map_add
  map_smul' := (linear A).map_smul
  continuous_toFun := (linear A).continuous
  continuous_invFun := (linear A⁻¹).continuous

@[simp] theorem planeEquiv_apply (A : SL2) (p : Plane) : planeEquiv A p = act A p := rfl

@[simp] theorem planeEquiv_symm (A : SL2) : (planeEquiv A).symm = planeEquiv A⁻¹ := by
  apply ContinuousLinearEquiv.ext
  funext p
  rfl

theorem planeEquiv_one : planeEquiv (1 : SL2) = ContinuousLinearEquiv.refl ℝ Plane := by
  apply ContinuousLinearEquiv.ext
  funext p
  exact congrArg (fun f : Plane →L[ℝ] Plane => f p) linear_one

theorem planeEquiv_mul (A B : SL2) :
    planeEquiv (A * B) = (planeEquiv B).trans (planeEquiv A) := by
  apply ContinuousLinearEquiv.ext
  funext p
  exact congrArg (fun f : Plane →L[ℝ] Plane => f p) (linear_mul A B)

theorem planeEquiv_det (A : SL2) : LinearMap.det (planeEquiv A : Plane →ₗ[ℝ] Plane) = 1 := by
  have hlin : (planeEquiv A : Plane →ₗ[ℝ] Plane) =
      Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
        (A : Matrix (Fin 2) (Fin 2) ℝ) := by
    apply LinearMap.ext
    intro p
    change act A p = _
    rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ), Matrix.toLin_finTwoProd_apply]
    rfl
  rw [hlin, LinearMap.det_toLin]
  exact A.property

theorem continuous_action : Continuous (fun p : SL2 × Plane => planeEquiv p.1 p.2) := by
  change Continuous (fun p : SL2 × Plane => act p.1 p.2)
  unfold act
  fun_prop

end VeechDichotomy.LinearEquivalences
