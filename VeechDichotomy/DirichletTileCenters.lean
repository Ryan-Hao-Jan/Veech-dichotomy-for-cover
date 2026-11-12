module

public import VeechDichotomy.EffectiveDirichletTiles

/-! Actual tiles are the genuine Dirichlet regions centered at the
corresponding orbit points. Equality of tiles is exactly equality of
their actual centers, even before selecting a regular center. The
finitely many centers of tiles at a Dirichlet point are precisely the
actual nearest orbit centers, all at the same actual distance. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletTileCenters

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletTessellation
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem translate_region (Γ : Subgroup SL2) (p z : ℍ) (γ : Γ) (hz : z ∈ region Γ p) :
    γ • z ∈ region Γ (γ • p) := by
  intro δ
  have hpoint : δ • (γ • p) = γ • ((γ⁻¹ * δ * γ) • p) := by
    simp only [mul_smul, smul_inv_smul]
  rw [hpoint]
  change dist ((γ : SL2) • z) ((γ : SL2) • p) ≤
    dist ((γ : SL2) • z) ((γ : SL2) • ((γ⁻¹ * δ * γ) • p))
  rw [dist_smul, dist_smul]
  exact hz (γ⁻¹ * δ * γ)

theorem tile_eq_region_center (Γ : Subgroup SL2) (p : ℍ) (γ : Γ) : tile Γ p γ = region Γ (γ • p) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact translate_region Γ p z γ hz
  · intro z hz
    refine ⟨γ⁻¹ • z, ?_, smul_inv_smul γ z⟩
    simpa only [inv_smul_smul] using translate_region Γ (γ • p) z γ⁻¹ hz

theorem tile_eq_iff_center_eq (Γ : Subgroup SL2) (p : ℍ) (g h : Γ) :
    tile Γ p g = tile Γ p h ↔ g • p = h • p := by
  constructor
  · intro he
    have hgp : g • p ∈ tile Γ p g := ⟨p, center_mem Γ p, rfl⟩
    rw [he, tile_eq_region_center] at hgp
    have hd := hgp (g * h⁻¹)
    rw [mul_smul, inv_smul_smul, dist_self] at hd
    exact dist_le_zero.mp hd
  · intro he
    rw [tile_eq_region_center, tile_eq_region_center, he]

def centersAt (Γ : Subgroup SL2) (p z : ℍ) : Set ℍ :=
  {q | q ∈ MulAction.orbit Γ p ∧ z ∈ region Γ q}

theorem centersAt_eq_image (Γ : Subgroup SL2) (p z : ℍ) :
    centersAt Γ p z = (fun γ : Γ => γ • p) '' {γ : Γ | z ∈ tile Γ p γ} := by
  apply Subset.antisymm
  · rintro q ⟨⟨γ, hγ⟩, hq⟩
    change γ • p = q at hγ
    refine ⟨γ, ?_, hγ⟩
    change z ∈ tile Γ p γ
    rw [tile_eq_region_center, hγ]
    exact hq
  · rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨MulAction.mem_orbit p γ, by rwa [← tile_eq_region_center]⟩

theorem centersAt_finite (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : (centersAt Γ p z).Finite := by
  rw [centersAt_eq_image]
  exact ((locallyFinite_tiles Γ p).point_finite z).image (fun γ : Γ => γ • p)

theorem centersAt_iff_equal_distance (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ region Γ p) (q : ℍ) :
    q ∈ centersAt Γ p z ↔ q ∈ MulAction.orbit Γ p ∧ dist z q = dist z p := by
  constructor
  · rintro ⟨⟨γ, hγ⟩, hq⟩
    change γ • p = q at hγ
    have h₁ := hz γ
    rw [hγ] at h₁
    have h₂ := hq γ⁻¹
    rw [← hγ, inv_smul_smul] at h₂
    rw [hγ] at h₂
    exact ⟨⟨γ, hγ⟩, le_antisymm h₂ h₁⟩
  · rintro ⟨⟨γ, hγ⟩, heq⟩
    change γ • p = q at hγ
    refine ⟨⟨γ, hγ⟩, ?_⟩
    intro δ
    have hd := hz (δ * γ)
    rw [mul_smul, hγ, ← heq] at hd
    exact hd

end VeechDichotomy.DirichletTileCenters
