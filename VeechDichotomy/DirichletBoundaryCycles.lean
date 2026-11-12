module

public import VeechDichotomy.NativeFiniteCornerDeficitBudget
public import VeechDichotomy.HyperbolicDirichletInterior
public import VeechDichotomy.HyperbolicDirichletPointCycles

/-! Boundary congruence cycles of an actual regular-center Dirichlet
region remain on the boundary. One weak and one strict distance comparison
already force a relative element to fix the center. Actual distinct tiles
therefore have disjoint interiors, with the global action kernel retained. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletBoundaryCycles

open LinearGroup Set Topology HyperbolicDirichletRegions HyperbolicStrictDirichlet
open HyperbolicDirichletInterior HyperbolicDirichletTessellation HyperbolicRegularCenters
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem weak_strict_overlap_fixes (Γ : Subgroup SL2) (p z : ℍ) (γ : Γ)
    (hz : z ∈ region Γ p) (hγ : γ • z ∈ strictRegion Γ p) : γ • p = p := by
  by_contra hfix
  have h₁ := hz γ⁻¹
  have h₂ := hγ γ hfix
  change dist z p ≤ dist z ((γ : SL2)⁻¹ • p) at h₁
  change dist ((γ : SL2) • z) p < dist ((γ : SL2) • z) ((γ : SL2) • p) at h₂
  rw [dist_smul] at h₂
  have hm : dist ((γ : SL2) • z) p = dist z ((γ : SL2)⁻¹ • p) := by
    simpa only [smul_inv_smul] using dist_smul (γ : SL2) z ((γ : SL2)⁻¹ • p)
  rw [← hm] at h₁
  exact not_lt_of_ge h₁ h₂

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem frontier_translate (p : ℍ) (hp : RegularCenter Γ p) (γ : Γ) {z : ℍ}
    (hz : z ∈ frontier (region Γ p)) (hγz : γ • z ∈ region Γ p) : γ • z ∈ frontier (region Γ p) := by
  apply (mem_frontier_iff_notMem_interior hγz).mpr
  intro hint
  have hs : γ • z ∈ strictRegion Γ p := by rwa [← interior_eq_strict Γ p]
  have hfix := weak_strict_overlap_fixes Γ p z γ ((isClosed_region Γ p).frontier_subset hz) hs
  have htrivial := hp γ hfix
  rw [htrivial z] at hint
  exact (mem_frontier_iff_notMem_interior ((isClosed_region Γ p).frontier_subset hz)).mp hz hint

theorem cycle_subset_frontier (p : ℍ) (hp : RegularCenter Γ p) {z : ℍ}
    (hz : z ∈ frontier (region Γ p)) :
    region Γ p ∩ MulAction.orbit Γ z ⊆ frontier (region Γ p) := by
  rintro w ⟨hw, γ, hγ⟩
  change γ • z = w at hγ
  rw [← hγ] at hw ⊢
  exact frontier_translate Γ p hp γ hz hw

theorem interior_tile (p : ℍ) (γ : Γ) :
    interior (tile Γ p γ) = (fun z : ℍ => γ • z) '' strictRegion Γ p := by
  change interior ((Homeomorph.smul γ : ℍ ≃ₜ ℍ) '' region Γ p) =
    (Homeomorph.smul γ : ℍ ≃ₜ ℍ) '' strictRegion Γ p
  rw [← (Homeomorph.smul γ : ℍ ≃ₜ ℍ).image_interior, interior_eq_strict Γ p]

theorem interior_overlap_tile_eq (p : ℍ) (hp : RegularCenter Γ p) (g h : Γ) {z : ℍ}
    (hg : z ∈ interior (tile Γ p g)) (hh : z ∈ interior (tile Γ p h)) : tile Γ p g = tile Γ p h := by
  rw [interior_tile] at hg hh
  obtain ⟨u, hu, hgu⟩ := hg
  obtain ⟨v, hv, hhv⟩ := hh
  have hgz : g⁻¹ • z ∈ strictRegion Γ p := by rw [← hgu, inv_smul_smul]; exact hu
  have hhz : h⁻¹ • z ∈ strictRegion Γ p := by rw [← hhv, inv_smul_smul]; exact hv
  have hfix : (g⁻¹ * h) • p = p := by
    simpa only [inv_inv] using relative_fixes Γ p z g⁻¹ h⁻¹ hgz hhz
  have htrivial := hp (g⁻¹ * h) hfix
  have hactions : (fun w : ℍ => g • w) = (fun w : ℍ => h • w) := by
    funext w
    have he := congrArg (fun x : ℍ => g • x) (htrivial w)
    simpa only [mul_smul, smul_inv_smul] using he.symm
  unfold tile
  rw [hactions]

theorem disjoint_interiors (p : ℍ) (hp : RegularCenter Γ p) (g h : Γ)
    (hne : tile Γ p g ≠ tile Γ p h) : Disjoint (interior (tile Γ p g)) (interior (tile Γ p h)) := by
  apply disjoint_left.mpr
  intro z hg hh
  exact hne (interior_overlap_tile_eq Γ p hp g h hg hh)

end VeechDichotomy.DirichletBoundaryCycles
