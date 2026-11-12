module

public import VeechDichotomy.SL2Borel
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Conformal

/-! Actual SL2 Mobius maps preserve actual tangent angles at every
genuine upper-half-plane point. The proved complex derivative is
nonzero, hence actually conformal as a real derivative. Chain rules
identify derivatives of actual mapped H-curves with this same real map.
No angle-preservation or conformality oracle is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicMobiusAngles

open LinearGroup Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def extension (A : SL2) (w : ℂ) : ℂ := (A • UpperHalfPlane.ofComplex w : ℍ)

def coefficient (A : SL2) (z : ℍ) : ℂ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ A).val.det / UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ A) z ^ 2

theorem determinant_pos (A : SL2) : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ A).val.det := by
  change 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).det
  rw [A.property]
  norm_num

theorem extension_coe (A : SL2) (z : ℍ) : extension A (z : ℂ) = ((A • z : ℍ) : ℂ) := by
  simp [extension]

theorem hasStrictDerivAt_extension (A : SL2) (z : ℍ) :
    HasStrictDerivAt (extension A) (coefficient A z) (z : ℂ) :=
  UpperHalfPlane.hasStrictDerivAt_smul (determinant_pos A) z

theorem deriv_extension_ne_zero (A : SL2) (z : ℍ) : deriv (extension A) (z : ℂ) ≠ 0 :=
  UpperHalfPlane.deriv_smul_ne_zero (determinant_pos A) z

theorem conformal_extension (A : SL2) (z : ℍ) : ConformalAt (extension A) (z : ℂ) :=
  (hasStrictDerivAt_extension A z).hasDerivAt.differentiableAt.conformalAt (deriv_extension_ne_zero A z)

theorem hasFDerivAt_extension_real (A : SL2) (z : ℍ) :
    HasFDerivAt (extension A) (fderiv ℝ (extension A) (z : ℂ)) (z : ℂ) :=
  ((hasStrictDerivAt_extension A z).hasDerivAt.hasFDerivAt.restrictScalars ℝ).differentiableAt.hasFDerivAt

theorem preserves_tangent_angles (A : SL2) (z : ℍ) (u v : ℂ) :
    InnerProductGeometry.angle ((fderiv ℝ (extension A) (z : ℂ)) u) ((fderiv ℝ (extension A) (z : ℂ)) v) =
      InnerProductGeometry.angle u v :=
  InnerProductGeometry.ConformalAt.preserves_angle (hasFDerivAt_extension_real A z) (conformal_extension A z) u v

theorem hasDerivAt_mapped_curve (A : SL2) (f : ℝ → ℍ) (t : ℝ) (v : ℂ)
    (hf : HasDerivAt (fun r : ℝ => (f r : ℂ)) v t) :
    HasDerivAt (fun r : ℝ => ((A • f r : ℍ) : ℂ)) ((fderiv ℝ (extension A) (f t : ℂ)) v) t := by
  have h := (hasFDerivAt_extension_real A (f t)).comp_hasDerivAt t hf
  have heq : (extension A ∘ fun r : ℝ => (f r : ℂ)) = fun r : ℝ => ((A • f r : ℍ) : ℂ) :=
    funext (fun r => extension_coe A (f r))
  rwa [heq] at h

end VeechDichotomy.HyperbolicMobiusAngles
