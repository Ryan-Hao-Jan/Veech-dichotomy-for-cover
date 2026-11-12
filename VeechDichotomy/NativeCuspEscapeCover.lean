module

public import VeechDichotomy.NativeCuspCompactCore
public import VeechDichotomy.CompactHyperbolicCoreQuotient

/-! Actual escape in the actual right lattice quotient eventually
places the inverse hyperbolic projection in the actual cusp-horoball
cover. Compactness of the constructed core discharges this implication. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCuspEscapeCover

open LinearGroup Set Filter Topology HyperbolicRegularCenters HyperbolicDirichletRegions
open DirichletIdealRadialPoints NativeCompatibleHoroballs NativeCuspCompactCore
open CompactHyperbolicCoreQuotient
open scoped UpperHalfPlane

def cover (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) (R : ℝ) : Set ℍ :=
  ⋃ u : idealBoundary Γ p, ⋃ γ : Γ, tile Γ hΓ p hp R u γ

theorem outside_cover_in_core_orbit (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ)
    (hp : RegularCenter Γ p) (R : ℝ) (x : ℍ) (hx : x ∉ cover Γ hΓ p hp R) :
    ∃ (γ : Γ) (z : ℍ), z ∈ core Γ hΓ p hp R ∧ x = γ • z := by
  let : DiscreteTopology Γ := hΓ.1
  have hm : x ∈ ⋃ γ : Γ, HyperbolicDirichletTessellation.tile Γ p γ := by
    rw [HyperbolicDirichletTessellation.tiles_cover]
    exact mem_univ _
  obtain ⟨γ, z, hz, he⟩ := mem_iUnion.mp hm
  change γ • z = x at he
  refine ⟨γ, z, ⟨hz, ?_⟩, he.symm⟩
  intro hbase
  obtain ⟨u, hu⟩ := mem_iUnion.mp hbase
  exact hx (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨γ, z, hu, he⟩⟩)

theorem outside_compact_in_cover (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ)
    (hp : RegularCenter Γ p) (R : ℝ) (g : SL2)
    (hg : (QuotientGroup.mk g : SL2 ⧸ Γ) ∉ coreQuotient Γ (core Γ hΓ p hp R)) :
    g⁻¹ • UpperHalfPlane.I ∈ cover Γ hΓ p hp R := by
  by_contra hx
  obtain ⟨γ, z, hz, he⟩ := outside_cover_in_core_orbit Γ hΓ p hp R (g⁻¹ • UpperHalfPlane.I) hx
  exact hg (mem_coreQuotient Γ _ g γ z hz he)

theorem eventually_covered (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ)
    (hp : RegularCenter Γ p) (R : ℝ) (g : ℝ → SL2)
    (hescape : Tendsto (fun t => (QuotientGroup.mk (g t) : SL2 ⧸ Γ)) atTop (cocompact (SL2 ⧸ Γ))) :
    ∀ᶠ t in atTop, ∃ (u : idealBoundary Γ p) (γ : Γ), (g t)⁻¹ • UpperHalfPlane.I ∈ tile Γ hΓ p hp R u γ := by
  have hcompact := isCompact_coreQuotient Γ (isCompact_core Γ hΓ p hp R)
  have hev := hescape.eventually hcompact.compl_mem_cocompact
  filter_upwards [hev] with t ht
  have hc := outside_compact_in_cover Γ hΓ p hp R (g t) ht
  obtain ⟨u, hu⟩ := mem_iUnion.mp hc
  obtain ⟨γ, hγ⟩ := mem_iUnion.mp hu
  exact ⟨u, γ, hγ⟩

end VeechDichotomy.NativeCuspEscapeCover
