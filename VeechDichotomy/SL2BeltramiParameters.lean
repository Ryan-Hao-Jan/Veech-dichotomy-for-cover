module

public import VeechDichotomy.SL2PowerLift
public import VeechDichotomy.BeltramiPlane

/-! Actual SL2 maps have continuously varying complex coefficients
A(z)=c*z+d*conj(z), with |c|^2-|d|^2=1. Thus c is nonzero and mu=d/c
lies in the complex unit disk. Compact SL2 sets give compact parameters. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2BeltramiParameters

open LinearGroup SL2PowerLift Set Topology

set_option backward.isDefEq.respectTransparency false

def scalar (A : SL2) : ℂ := (firstColumn A - Complex.I * secondColumn A) / 2
def antiScalar (A : SL2) : ℂ := (firstColumn A + Complex.I * secondColumn A) / 2

theorem action_formula (A : SL2) (z : ℂ) :
    complexAction A z = scalar A * z + antiScalar A * star z := by
  rw [complexAction_columns]
  apply Complex.ext <;> simp [scalar, antiScalar, firstColumn, secondColumn] <;> ring

theorem normSq_difference (A : SL2) : Complex.normSq (scalar A) - Complex.normSq (antiScalar A) = 1 := by
  have hd := A.property
  rw [Matrix.det_fin_two] at hd
  simp [scalar, antiScalar, firstColumn, secondColumn, Complex.normSq_apply]
  nlinarith [hd]

theorem norm_difference (A : SL2) : ‖scalar A‖ ^ 2 - ‖antiScalar A‖ ^ 2 = 1 := by
  simpa only [Complex.normSq_eq_norm_sq] using normSq_difference A

theorem scalar_ne_zero (A : SL2) : scalar A ≠ 0 := by
  intro hz
  have h := norm_difference A
  rw [hz, norm_zero] at h
  nlinarith [sq_nonneg ‖antiScalar A‖]

theorem anti_norm_lt (A : SL2) : ‖antiScalar A‖ < ‖scalar A‖ := by
  have h := norm_difference A
  nlinarith [norm_nonneg (scalar A), norm_nonneg (antiScalar A)]

def parameter (A : SL2) : BeltramiPlane.Parameter :=
  ⟨antiScalar A / scalar A, by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr (scalar_ne_zero A))).mpr (anti_norm_lt A)⟩

theorem factorization (A : SL2) (z : ℂ) : complexAction A z = scalar A * BeltramiPlane.map (parameter A).val z := by
  rw [action_formula]
  change scalar A * z + antiScalar A * star z = scalar A * (z + (antiScalar A / scalar A) * star z)
  field_simp [scalar_ne_zero A]

theorem continuous_firstColumn : Continuous firstColumn := by
  change Continuous (fun A : SL2 => Complex.equivRealProdCLM.symm (A.1 0 0, A.1 1 0))
  exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)

theorem continuous_secondColumn : Continuous secondColumn := by
  change Continuous (fun A : SL2 => Complex.equivRealProdCLM.symm (A.1 0 1, A.1 1 1))
  exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)

theorem continuous_scalar : Continuous scalar := by
  exact (continuous_firstColumn.sub (continuous_const.mul continuous_secondColumn)).div_const 2

theorem continuous_antiScalar : Continuous antiScalar := by
  exact (continuous_firstColumn.add (continuous_const.mul continuous_secondColumn)).div_const 2

theorem continuous_parameter : Continuous parameter :=
  (continuous_antiScalar.div continuous_scalar scalar_ne_zero).subtype_mk _

theorem compact_parameters {K : Set SL2} (hK : IsCompact K) :
    IsCompact ((fun A => (scalar A, parameter A)) '' K) :=
  hK.image (continuous_scalar.prodMk continuous_parameter)

end VeechDichotomy.SL2BeltramiParameters
