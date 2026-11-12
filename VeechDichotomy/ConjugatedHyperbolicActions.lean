module

public import VeechDichotomy.NativeLatticeConjugation
public import VeechDichotomy.HyperbolicDirichletRegions

/-! Genuine ambient conjugation intertwines the actual hyperbolic
actions and transports the entire actual Dirichlet region. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ConjugatedHyperbolicActions

open LinearGroup NativeLatticeConjugation HyperbolicDirichletRegions Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def toConjugate (Γ : Subgroup SL2) (B : SL2) (γ : Γ) : conjugate Γ B :=
  ⟨B * (γ : SL2) * B⁻¹, by
    change B⁻¹ * (B * (γ : SL2) * B⁻¹) * B ∈ Γ
    have he : B⁻¹ * (B * (γ : SL2) * B⁻¹) * B = γ := by group
    rw [he]
    exact γ.property⟩

theorem conjugate_smul (Γ : Subgroup SL2) (B : SL2) (γ : Γ) (z : ℍ) :
    toConjugate Γ B γ • (B • z) = B • (γ • z) := by
  change (B * (γ : SL2) * B⁻¹) • (B • z) = B • ((γ : SL2) • z)
  rw [mul_smul, inv_smul_smul, mul_smul]

theorem original_smul (Γ : Subgroup SL2) (B : SL2) (δ : conjugate Γ B) (z : ℍ) :
    δ • (B • z) = B • (toOriginal Γ B δ • z) := by
  change (δ : SL2) • (B • z) = B • ((B⁻¹ * (δ : SL2) * B) • z)
  simp only [mul_smul, smul_inv_smul]

theorem mem_region_iff (Γ : Subgroup SL2) (B : SL2) (p z : ℍ) :
    B • z ∈ region (conjugate Γ B) (B • p) ↔ z ∈ region Γ p := by
  constructor
  · intro hz γ
    have h := hz (toConjugate Γ B γ)
    rw [conjugate_smul Γ B γ p] at h
    simpa only [dist_smul] using! h
  · intro hz δ
    rw [original_smul Γ B δ p]
    simpa only [dist_smul] using! hz (toOriginal Γ B δ)

theorem image_region (Γ : Subgroup SL2) (B : SL2) (p : ℍ) :
    (fun z : ℍ => B • z) '' region Γ p = region (conjugate Γ B) (B • p) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (mem_region_iff Γ B p z).mpr hz
  · intro w hw
    refine ⟨B⁻¹ • w, ?_, smul_inv_smul B w⟩
    apply (mem_region_iff Γ B p _).mp
    simpa only [smul_inv_smul] using hw

end VeechDichotomy.ConjugatedHyperbolicActions
