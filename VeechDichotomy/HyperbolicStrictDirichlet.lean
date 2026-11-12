module

public import VeechDichotomy.HyperbolicDirichletLocalFiniteness

/-! The actual strict Dirichlet region allows repetitions of its center
under a finite stabilizer. Distinct translates can overlap only through
that stabilizer, proved directly from genuine strict metric inequalities.
No torsion-free or generic-center assumption is imposed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicStrictDirichlet

open LinearGroup HyperbolicDirichletRegions Set
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2)

def strictRegion (p : ℍ) : Set ℍ := {z | ∀ γ : Γ, γ • p ≠ p → dist z p < dist z (γ • p)}

theorem subset_region (p : ℍ) : strictRegion Γ p ⊆ region Γ p := by
  intro z hz γ
  by_cases hfix : γ • p = p
  · rw [hfix]
  · exact (hz γ hfix).le

theorem measurable_strictRegion [Countable Γ] (p : ℍ) : MeasurableSet (strictRegion Γ p) := by
  classical
  have heq : strictRegion Γ p = ⋂ γ : Γ, {z : ℍ | γ • p ≠ p → dist z p < dist z (γ • p)} := by
    ext z
    simp [strictRegion]
  rw [heq]
  apply MeasurableSet.iInter
  intro γ
  by_cases hfix : γ • p = p
  · simp only [hfix, ne_eq, not_true_eq_false, false_implies, ofPred_true, MeasurableSet.univ]
  · have heq : {z : ℍ | γ • p ≠ p → dist z p < dist z (γ • p)} =
        {z : ℍ | dist z p < dist z (γ • p)} := by
      ext z
      simp [hfix]
    rw [heq]
    exact (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)).measurableSet

theorem overlap_fixes (p z : ℍ) (γ : Γ) (hz : z ∈ strictRegion Γ p)
    (hγ : γ • z ∈ strictRegion Γ p) : γ • p = p := by
  by_contra hfix
  have hrev : γ⁻¹ • p ≠ p := by
    intro he
    apply hfix
    have h := congrArg (fun w : ℍ => γ • w) he
    simpa only [smul_inv_smul] using h.symm
  have h₁ := hz γ⁻¹ hrev
  have h₂ := hγ γ hfix
  change dist z p < dist z ((γ : SL2)⁻¹ • p) at h₁
  change dist ((γ : SL2) • z) p < dist ((γ : SL2) • z) ((γ : SL2) • p) at h₂
  rw [dist_smul] at h₂
  have hm : dist ((γ : SL2) • z) p = dist z ((γ : SL2)⁻¹ • p) := by
    simpa only [smul_inv_smul] using dist_smul (γ : SL2) z ((γ : SL2)⁻¹ • p)
  rw [← hm] at h₁
  exact lt_asymm h₁ h₂

theorem relative_fixes (p z : ℍ) (g h : Γ) (hg : g • z ∈ strictRegion Γ p)
    (hh : h • z ∈ strictRegion Γ p) : (g * h⁻¹) • p = p := by
  apply overlap_fixes Γ p (h • z) (g * h⁻¹) hh
  simpa only [mul_smul, inv_smul_smul] using hg

theorem stabilizer_finite [DiscreteTopology Γ] (p : ℍ) : {γ : Γ | γ • p = p}.Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer' Γ p

end VeechDichotomy.HyperbolicStrictDirichlet
