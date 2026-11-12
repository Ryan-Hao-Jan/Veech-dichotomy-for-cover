module

public import VeechDichotomy.CircleNormalFanAngleSum

/-! The actual finite Dirichlet fan at a boundary point has total
angular width 2*pi. Actual nearest sites give the genuine equal-radius
normal fan, and the proved effective multiplicity then gives the exact
point-cycle angle sum 2*pi/m. No angle-cycle interface or axiom is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDirichletCycleAngles

open LinearGroup Set HyperbolicDirichletRegions HyperbolicRegularCenters DirichletTileCenters
open HyperbolicNearestSiteVectors DirichletNearestSiteCones HyperbolicRegionAngles FiniteSiteNormalFans
open EffectivePointStabilizers EffectiveDirichletTiles EffectiveCycleSums TileCenterEquivalence
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def siteMap (Γ : Subgroup SL2) (p z : ℍ) (q : centersAt Γ p z) : sites Γ p z :=
  ⟨site z q.val, q.val, q.property, rfl⟩

theorem siteMap_bijective (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ region Γ p) :
    Function.Bijective (siteMap Γ p z) := by
  constructor
  · intro q r he
    apply Subtype.ext
    exact site_injective Γ p z hz q.property r.property (congrArg Subtype.val he)
  · intro s
    obtain ⟨q, hq, he⟩ := s.property
    exact ⟨⟨q, hq⟩, Subtype.ext he⟩

noncomputable instance sitesFintype (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : Fintype (sites Γ p z) :=
  (sites_finite Γ p z).fintype

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem boundary_sites_card (p z : ℍ) (hz : z ∈ frontier (region Γ p)) : 2 ≤ Fintype.card (sites Γ p z) := by
  have hzD : z ∈ region Γ p := (isClosed_region Γ p).frontier_subset hz
  have hbase := base_site_mem Γ p z hzD
  obtain ⟨u, hu, hne⟩ := boundary_other_site Γ p z hz
  exact Fintype.one_lt_card_iff.mpr ⟨⟨u, hu⟩, ⟨site z p, hbase⟩,
    fun he => hne (congrArg Subtype.val he)⟩

theorem center_width_sum_two_pi (p z : ℍ) (hz : z ∈ frontier (region Γ p)) :
    (∑ q : centersAt Γ p z, DirichletCornerAngles.width Γ q.val z) = 2 * Real.pi := by
  classical
  have hzD : z ∈ region Γ p := (isClosed_region Γ p).frontier_subset hz
  let e : centersAt Γ p z ≃ sites Γ p z := Equiv.ofBijective (siteMap Γ p z) (siteMap_bijective Γ p z hzD)
  calc
    _ = ∑ q : centersAt Γ p z, vectorWidth (sector (sites Γ p z) (site z q.val)) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [DirichletConeAngles.width_eq Γ q.val z q.property.2,
        DirichletPhysicalFan.physicalCone_sector Γ p q.val z q.property.1 q.property.2]
    _ = ∑ s : sites Γ p z, vectorWidth (sector (sites Γ p z) s.val) :=
      e.sum_comp (fun s : sites Γ p z => vectorWidth (sector (sites Γ p z) s.val))
    _ = 2 * Real.pi := CircleNormalFanAngleSum.sum_widths_fintype (sites Γ p z) (Real.sinh (dist z p))
      (boundary_radius_pos Γ p z hz) (sites_on_circle Γ p z hzD) (boundary_sites_card Γ p z hz)

theorem tile_width_sum_two_pi (p z : ℍ) (hz : z ∈ frontier (region Γ p)) :
    (∑ T : tilesAt Γ p z, pointWidth T.val z) = 2 * Real.pi := by
  rw [← width_sum_centers_eq_tiles Γ p z]
  exact center_width_sum_two_pi Γ p z hz

theorem effective_cycle_identity (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (hz : z ∈ frontier (region Γ p)) :
    (effectiveOrder Γ z : ℝ) * (∑ w : cycle Γ p z, DirichletCornerAngles.width Γ p w.val) = 2 * Real.pi := by
  rw [← EffectiveCycleMultiplicity.center_width_sum Γ p hp z]
  exact center_width_sum_two_pi Γ p z hz

theorem cycle_width_sum (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (hz : z ∈ frontier (region Γ p)) :
    (∑ w : cycle Γ p z, DirichletCornerAngles.width Γ p w.val) = 2 * Real.pi / (effectiveOrder Γ z : ℝ) := by
  rw [EffectiveCycleMultiplicity.cycle_width_sum_eq_div Γ p hp z, center_width_sum_two_pi Γ p z hz]

end VeechDichotomy.NativeDirichletCycleAngles
