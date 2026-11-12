module

public import VeechDichotomy.DiscreteQuotientContraction
public import VeechDichotomy.NativeShearMatrices
public import VeechDichotomy.NativeLatticeRecurrence

/-! Every nontrivial lower unipotent is genuinely contracted by the
native diagonal ray. For a discrete subgroup containing its conjugate,
the corresponding actual quotient ray diverges. This is the elementary
parabolic-to-escape direction; NativeLatticePointwiseCusp proves the
finite-volume converse for every specified diagonal ray. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2ParabolicRayEscape

open NativeVeech NativeShearMatrices NativeTeichmullerRay LinearGroup Filter Topology

set_option backward.isDefEq.respectTransparency false

theorem continuous_lower : Continuous lower := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lower] <;> fun_prop

theorem diagonal_inverse (t : ℝ) : (diagonal t)⁻¹ = diagonal (-t) := by
  have hprod : diagonal t * diagonal (-t) = 1 := by
    rw [← diagonal_add, add_neg_cancel, NativeLatticeRecurrence.diagonal_zero]
  calc
    (diagonal t)⁻¹ = (diagonal t)⁻¹ * (diagonal t * diagonal (-t)) := by rw [hprod, mul_one]
    _ = diagonal (-t) := by group

theorem conjugate_lower (t a : ℝ) :
    diagonal t * lower a * (diagonal t)⁻¹ = lower (Real.exp (-t) * Real.exp (-t) * a) := by
  rw [diagonal_inverse]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, lower, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Real.exp_neg]
  ring

theorem contracted (a : ℝ) :
    Tendsto (fun t => diagonal t * lower a * (diagonal t)⁻¹) atTop (𝓝 (1 : SL2)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hs : Tendsto (fun t : ℝ => Real.exp (-t) * Real.exp (-t) * a) atTop (𝓝 0) := by
    simpa only [zero_mul] using (he.mul he).mul_const a
  have heq : (fun t => diagonal t * lower a * (diagonal t)⁻¹) =
      fun t => lower (Real.exp (-t) * Real.exp (-t) * a) := funext fun t => conjugate_lower t a
  rw [heq]
  simpa only [lower_zero, Function.comp_def] using! (continuous_lower.tendsto 0).comp hs

theorem divergent (Γ : Subgroup SL2) [DiscreteTopology Γ] (A : SL2)
    {a : ℝ} (ha : a ≠ 0) (hmem : A⁻¹ * lower a * A ∈ Γ) :
    Tendsto (fun t => (QuotientGroup.mk (diagonal t * A) : SL2 ⧸ Γ)) atTop
      (cocompact (SL2 ⧸ Γ)) := by
  have hne : A⁻¹ * lower a * A ≠ 1 := by
    intro h
    apply ne_one ha
    calc
      lower a = A * (A⁻¹ * lower a * A) * A⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hc : Tendsto (fun t => (diagonal t * A) * (A⁻¹ * lower a * A) * (diagonal t * A)⁻¹)
      atTop (𝓝 (1 : SL2)) := by
    have heq : (fun t => (diagonal t * A) * (A⁻¹ * lower a * A) * (diagonal t * A)⁻¹) =
        fun t => diagonal t * lower a * (diagonal t)⁻¹ := by funext t; group
    rw [heq]
    exact contracted a
  exact DiscreteQuotientContraction.divergent Γ (fun t => diagonal t * A) hmem hne hc

end VeechDichotomy.SL2ParabolicRayEscape
