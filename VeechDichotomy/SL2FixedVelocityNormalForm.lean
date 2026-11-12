module

public import VeechDichotomy.NativeShearMatrices

/-! An actual determinant-one real matrix fixing a nonzero vector has
the exact lower-unipotent normal form in coordinates sending that vector
to the vertical axis. Nonidentity is exactly a nonzero shear parameter. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2FixedVelocityNormalForm

open MNEC.LatticeTorus NativeVeech NativeShearMatrices NativePrimitiveRectangles
open LinearGroup LinearEquivalences

set_option backward.isDefEq.respectTransparency false

theorem vertical_normal_form (B : SL2) (hfix : planeEquiv B vertical = vertical) :
    B = lower (B 1 0) := by
  have h01 : B 0 1 = 0 := by
    have h := congrArg Prod.fst hfix
    simpa [planeEquiv_apply, act, vertical] using h
  have h11 : B 1 1 = 1 := by
    have h := congrArg Prod.snd hfix
    simpa [planeEquiv_apply, act, vertical] using h
  have hd := B.property
  rw [Matrix.det_fin_two] at hd
  have h00 : B 0 0 = 1 := by simpa only [h01, h11, mul_one, zero_mul, sub_zero] using hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, h00, h01, h11]

theorem conjugate_normal_form (A B : SL2) (v : Plane) {c : ℝ} (hc : c ≠ 0)
    (hAv : planeEquiv A v = c • vertical) (hBv : planeEquiv B v = v) :
    ∃ a : ℝ, B = A⁻¹ * lower a * A := by
  let C := A * B * A⁻¹
  have hC : planeEquiv C (planeEquiv A v) = planeEquiv A v := by
    dsimp only [C]
    simp only [planeEquiv_mul, ContinuousLinearEquiv.trans_apply, ← planeEquiv_symm,
      ContinuousLinearEquiv.symm_apply_apply, hBv]
  rw [hAv, map_smul] at hC
  have hvertical : planeEquiv C vertical = vertical := by
    have h := congrArg (fun p : Plane => c⁻¹ • p) hC
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  refine ⟨C 1 0, ?_⟩
  have hnormal := vertical_normal_form C hvertical
  calc
    B = A⁻¹ * C * A := by dsimp only [C]; group
    _ = A⁻¹ * lower (C 1 0) * A := congrArg (fun D : SL2 => A⁻¹ * D * A) hnormal

theorem nontrivial_conjugate_normal_form (A B : SL2) (v : Plane) {c : ℝ} (hc : c ≠ 0)
    (hAv : planeEquiv A v = c • vertical) (hBv : planeEquiv B v = v) (hne : B ≠ 1) :
    ∃ a : ℝ, a ≠ 0 ∧ B = A⁻¹ * lower a * A := by
  obtain ⟨a, ha⟩ := conjugate_normal_form A B v hc hAv hBv
  refine ⟨a, ?_, ha⟩
  intro ha0
  apply hne
  rw [ha, ha0, lower_zero]
  group

end VeechDichotomy.SL2FixedVelocityNormalForm
