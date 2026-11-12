module

public import VeechDichotomy.HyperbolicDirichletTessellation
public import VeechDichotomy.HyperbolicRegularCenters

/-! Congruence cycles of actual points in a Dirichlet region are finite.
The locally finite actual tile family supplies a finite list of labels
meeting a point; inverse labels enumerate the cycle. At a regular center,
a label preserves the entire region exactly when it acts trivially on
the plane, retaining the actual SL2 center without assuming faithfulness. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletPointCycles

open LinearGroup HyperbolicDirichletRegions HyperbolicDirichletTessellation
open HyperbolicRegularCenters Set
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2)

theorem center_orbit_mem_iff (p : ℍ) (γ : Γ) : γ • p ∈ region Γ p ↔ γ • p = p := by
  constructor
  · intro hz
    have h := hz γ
    rw [dist_self] at h
    exact dist_le_zero.mp h
  · intro hfix
    rw [hfix]
    exact center_mem Γ p

theorem tile_eq_region_iff_trivial (p : ℍ) (hp : RegularCenter Γ p) (γ : Γ) :
    tile Γ p γ = region Γ p ↔ ∀ z : ℍ, γ • z = z := by
  constructor
  · intro heq
    apply hp γ
    apply (center_orbit_mem_iff Γ p γ).mp
    rw [← heq]
    exact ⟨p, center_mem Γ p, rfl⟩
  · intro htrivial
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact ((htrivial w).symm.trans hwz) ▸ hw
    · intro hz
      exact ⟨z, hz, htrivial z⟩

variable [DiscreteTopology Γ]

theorem cycle_finite (p z : ℍ) : (region Γ p ∩ MulAction.orbit Γ z).Finite := by
  have hf : {γ : Γ | z ∈ tile Γ p γ}.Finite := (locallyFinite_tiles Γ p).point_finite z
  apply (hf.image (fun γ : Γ => γ⁻¹ • z)).subset
  intro w hw
  obtain ⟨δ, hδ⟩ := hw.2
  change δ • z = w at hδ
  refine ⟨δ⁻¹, ?_, ?_⟩
  · refine ⟨w, hw.1, ?_⟩
    change δ⁻¹ • w = z
    rw [← hδ, inv_smul_smul]
  · simpa only [inv_inv] using hδ

end VeechDichotomy.HyperbolicDirichletPointCycles
