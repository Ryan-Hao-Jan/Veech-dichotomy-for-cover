module

public import VeechDichotomy.DirichletNoncornerWidth

/-! Actual distinct tiles and their actual point-cycle representatives.
At a regular center equality of entire tiles is exactly equality of the
global actions, retaining the ineffective SL2 kernel. Finite distinct
tiles at a point map onto its actual finite congruence cycle, and their
actual angular widths are the corresponding Dirichlet widths. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.EffectiveDirichletTiles

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletTessellation HyperbolicDirichletPointCycles
open HyperbolicRegularCenters HyperbolicRegionAngles
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem image_tile (Γ : Subgroup SL2) (p : ℍ) (g h : Γ) :
    (fun z : ℍ => g • z) '' tile Γ p h = tile Γ p (g * h) := by
  unfold tile
  simp only [image_image, mul_smul]

theorem tile_one (Γ : Subgroup SL2) (p : ℍ) : tile Γ p 1 = region Γ p := by simp [tile]

theorem tile_eq_iff_relative_trivial (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (g h : Γ) :
    tile Γ p g = tile Γ p h ↔ ∀ z : ℍ, (h⁻¹ * g) • z = z := by
  constructor
  · intro he
    have hi := congrArg (fun S : Set ℍ => (fun z : ℍ => h⁻¹ • z) '' S) he
    rw [image_tile, image_tile, inv_mul_cancel, tile_one] at hi
    exact (tile_eq_region_iff_trivial Γ p hp (h⁻¹ * g)).mp hi
  · intro htrivial
    have hactions : (fun z : ℍ => g • z) = (fun z : ℍ => h • z) := by
      funext z
      have he := congrArg (fun w : ℍ => h • w) (htrivial z)
      simpa only [mul_smul, smul_inv_smul] using he
    unfold tile
    rw [hactions]

theorem tile_eq_iff_actions_eq (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (g h : Γ) :
    tile Γ p g = tile Γ p h ↔ ∀ z : ℍ, g • z = h • z := by
  constructor
  · intro he z
    have htrivial := (tile_eq_iff_relative_trivial Γ p hp g h).mp he
    have hh := congrArg (fun w : ℍ => h • w) (htrivial z)
    simpa only [mul_smul, smul_inv_smul] using hh
  · intro he
    unfold tile
    rw [funext he]

def tilesAt (Γ : Subgroup SL2) (p z : ℍ) : Set (Set ℍ) :=
  tile Γ p '' {γ : Γ | z ∈ tile Γ p γ}

theorem tilesAt_finite (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : (tilesAt Γ p z).Finite :=
  ((locallyFinite_tiles Γ p).point_finite z).image (tile Γ p)

def representative (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : Γ := Classical.choose T.property

theorem representative_mem (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) :
    z ∈ tile Γ p (representative Γ p z T) := (Classical.choose_spec T.property).1

theorem representative_tile (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) :
    tile Γ p (representative Γ p z T) = T.val := (Classical.choose_spec T.property).2

def cyclePoint (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : ℍ := (representative Γ p z T)⁻¹ • z

theorem cyclePoint_eq_of_label (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ)
    (T : tilesAt Γ p z) (γ : Γ) (hγ : tile Γ p γ = T.val) : cyclePoint Γ p z T = γ⁻¹ • z := by
  have heq : tile Γ p (representative Γ p z T) = tile Γ p γ := (representative_tile Γ p z T).trans hγ.symm
  have hactions := (tile_eq_iff_actions_eq Γ p hp _ γ).mp heq
  apply MulAction.injective γ
  change γ • ((representative Γ p z T)⁻¹ • z) = γ • (γ⁻¹ • z)
  rw [smul_inv_smul, ← hactions ((representative Γ p z T)⁻¹ • z), smul_inv_smul]

theorem cyclePoint_mem_cycle (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) :
    cyclePoint Γ p z T ∈ region Γ p ∩ MulAction.orbit Γ z := by
  obtain ⟨w, hw, he⟩ := representative_mem Γ p z T
  have hpw : cyclePoint Γ p z T = w := by
    have h := congrArg (fun y : ℍ => (representative Γ p z T)⁻¹ • y) he
    change (representative Γ p z T)⁻¹ • ((representative Γ p z T) • w) = (representative Γ p z T)⁻¹ • z at h
    rw [inv_smul_smul] at h
    exact h.symm
  refine ⟨hpw.symm ▸ hw, ?_⟩
  exact MulAction.mem_orbit z ((representative Γ p z T)⁻¹)

theorem range_cyclePoint (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) :
    range (cyclePoint Γ p z) = region Γ p ∩ MulAction.orbit Γ z := by
  apply Subset.antisymm
  · rintro _ ⟨T, rfl⟩
    exact cyclePoint_mem_cycle Γ p z T
  · rintro w ⟨hw, δ, hδ⟩
    change δ • z = w at hδ
    have hlabel : z ∈ tile Γ p δ⁻¹ := ⟨w, hw, by change δ⁻¹ • w = z; rw [← hδ, inv_smul_smul]⟩
    let T : tilesAt Γ p z := ⟨tile Γ p δ⁻¹, δ⁻¹, hlabel, rfl⟩
    refine ⟨T, ?_⟩
    have he := cyclePoint_eq_of_label Γ p hp z T δ⁻¹ rfl
    rw [inv_inv] at he
    exact he.trans hδ

theorem cyclePoint_mem_frontier (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) (hp : RegularCenter Γ p)
    {z : ℍ} (hz : z ∈ frontier (region Γ p)) (T : tilesAt Γ p z) :
    cyclePoint Γ p z T ∈ frontier (region Γ p) :=
  DirichletBoundaryCycles.cycle_subset_frontier Γ p hp hz (cyclePoint_mem_cycle Γ p z T)

theorem tile_pointWidth (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) :
    pointWidth T.val z = DirichletCornerAngles.width Γ p (cyclePoint Γ p z T) := by
  have he := tile_width Γ p (cyclePoint Γ p z T) (representative Γ p z T)
  rw [cyclePoint, smul_inv_smul, representative_tile] at he
  exact he

end VeechDichotomy.EffectiveDirichletTiles
