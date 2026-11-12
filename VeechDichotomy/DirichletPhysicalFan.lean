module

public import VeechDichotomy.FiniteSiteNormalFans

/-! Actual local Dirichlet cones at a common point form a genuine
finite normal fan of distinct equal-radius sites. All orbit centers
use the same nearest-site set. The actual cones cover the plane and
have disjoint interiors, and each cone has nonempty interior. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletPhysicalFan

open LinearGroup Set HyperbolicDirichletRegions DirichletTileCenters HyperbolicNearestSiteVectors
open DirichletNearestSiteCones DirichletConeDirections FiniteSiteNormalFans
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem centersAt_eq_of_orbit (Γ : Subgroup SL2) (p q z : ℍ) (hq : q ∈ MulAction.orbit Γ p) :
    centersAt Γ q z = centersAt Γ p z := by
  obtain ⟨γ, hγ⟩ := hq
  change γ • p = q at hγ
  apply Subset.antisymm
  · rintro r ⟨⟨δ, hδ⟩, hr⟩
    change δ • q = r at hδ
    refine ⟨⟨δ * γ, ?_⟩, hr⟩
    change (δ * γ) • p = r
    rw [mul_smul, hγ]
    exact hδ
  · rintro r ⟨⟨δ, hδ⟩, hr⟩
    change δ • p = r at hδ
    refine ⟨⟨δ * γ⁻¹, ?_⟩, hr⟩
    change (δ * γ⁻¹) • q = r
    rw [← hγ, mul_smul, inv_smul_smul]
    exact hδ

theorem sites_eq_of_orbit (Γ : Subgroup SL2) (p q z : ℍ) (hq : q ∈ MulAction.orbit Γ p) :
    sites Γ q z = sites Γ p z := by
  unfold sites
  rw [centersAt_eq_of_orbit Γ p q z hq]

theorem physicalCone_sector (Γ : Subgroup SL2) (p q z : ℍ) (hq : q ∈ MulAction.orbit Γ p)
    (hzq : z ∈ region Γ q) : physicalCone Γ q z = sector (sites Γ p z) (site z q) := by
  rw [physicalCone_eq_normalCone Γ q z hzq]
  ext u
  simp only [normalCone, sector, mem_ofPred_eq, functional_apply, sites_eq_of_orbit Γ p q z hq]

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem physical_cones_cover (p z : ℍ) (hz : z ∈ region Γ p) :
    (⋃ q ∈ centersAt Γ p z, physicalCone Γ q z) = univ := by
  ext u
  simp only [mem_iUnion, mem_univ, iff_true, exists_prop]
  obtain ⟨s, hs, hu⟩ := exists_sector (sites Γ p z) (sites_finite Γ p z) ⟨site z p, base_site_mem Γ p z hz⟩ u
  obtain ⟨q, hq, rfl⟩ := hs
  refine ⟨q, hq, ?_⟩
  rw [physicalCone_sector Γ p q z hq.1 hq.2]
  exact hu

omit [DiscreteTopology Γ] in
theorem physical_cone_interiors_disjoint (p z : ℍ) (hz : z ∈ region Γ p) {q r : ℍ}
    (hq : q ∈ centersAt Γ p z) (hr : r ∈ centersAt Γ p z) (hqr : q ≠ r) :
    Disjoint (interior (physicalCone Γ q z)) (interior (physicalCone Γ r z)) := by
  rw [physicalCone_sector Γ p q z hq.1 hq.2, physicalCone_sector Γ p r z hr.1 hr.2]
  apply FiniteSiteNormalFans.disjoint_interiors (V := sites Γ p z) (s := site z q) (t := site z r)
  · exact ⟨q, hq, rfl⟩
  · exact ⟨r, hr, rfl⟩
  · exact fun he => hqr (site_injective Γ p z hz hq hr he)

theorem site_sector_interior_nonempty (p z : ℍ) {s : ℂ} (hs : s ∈ sites Γ p z) :
    (interior (sector (sites Γ p z) s)).Nonempty := by
  obtain ⟨q, hq, rfl⟩ := hs
  rw [← physicalCone_sector Γ p q z hq.1 hq.2]
  exact physical_interior_nonempty Γ q z

end VeechDichotomy.DirichletPhysicalFan
