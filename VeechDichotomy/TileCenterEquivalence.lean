module

public import VeechDichotomy.EffectiveCycleSums

/-! Actual distinct tiles at a point are in genuine bijection with
the actual nearest orbit centers. This equivalence does not require
a regular center. It also identifies the actual tile angular width
with the Dirichlet width at its genuine center. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.TileCenterEquivalence

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletTessellation HyperbolicRegionAngles
open EffectiveDirichletTiles EffectiveStabilizerTiles DirichletTileCenters
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def center (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : ℍ := tileLabel Γ p z T • p

theorem center_mem (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : center Γ p z T ∈ centersAt Γ p z := by
  refine ⟨MulAction.mem_orbit p (tileLabel Γ p z T), ?_⟩
  change z ∈ region Γ (tileLabel Γ p z T • p)
  rw [← tile_eq_region_center]
  exact representative_mem Γ p z T

def centerMap (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : centersAt Γ p z :=
  ⟨center Γ p z T, center_mem Γ p z T⟩

theorem center_injective (Γ : Subgroup SL2) (p z : ℍ) : Function.Injective (center Γ p z) := by
  intro T U he
  have htiles := (tile_eq_iff_center_eq Γ p (tileLabel Γ p z T) (tileLabel Γ p z U)).mpr he
  apply Subtype.ext
  exact (representative_tile Γ p z T).symm.trans (htiles.trans (representative_tile Γ p z U))

theorem centerMap_bijective (Γ : Subgroup SL2) (p z : ℍ) : Function.Bijective (centerMap Γ p z) := by
  constructor
  · intro T U he
    exact center_injective Γ p z (congrArg Subtype.val he)
  · intro q
    obtain ⟨γ, hγ⟩ := q.property.1
    change γ • p = q.val at hγ
    have hz : z ∈ tile Γ p γ := by
      rw [tile_eq_region_center, hγ]
      exact q.property.2
    let T : tilesAt Γ p z := ⟨tile Γ p γ, γ, hz, rfl⟩
    refine ⟨T, Subtype.ext ?_⟩
    have htiles : tile Γ p (tileLabel Γ p z T) = tile Γ p γ := representative_tile Γ p z T
    have he := (tile_eq_iff_center_eq Γ p _ γ).mp htiles
    exact he.trans hγ

def equiv (Γ : Subgroup SL2) (p z : ℍ) : tilesAt Γ p z ≃ centersAt Γ p z :=
  Equiv.ofBijective (centerMap Γ p z) (centerMap_bijective Γ p z)

theorem tile_as_center (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : T.val = region Γ (center Γ p z T) := by
  rw [← representative_tile Γ p z T, tile_eq_region_center]
  rfl

theorem tile_pointWidth_center (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) :
    pointWidth T.val z = DirichletCornerAngles.width Γ (center Γ p z T) z := by
  calc
    _ = pointWidth (region Γ (center Γ p z T)) z := congrArg (fun S : Set ℍ => pointWidth S z) (tile_as_center Γ p z T)
    _ = _ := rfl

noncomputable instance centersFintype (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : Fintype (centersAt Γ p z) :=
  (centersAt_finite Γ p z).fintype

theorem width_sum_centers_eq_tiles (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) :
    (∑ q : centersAt Γ p z, DirichletCornerAngles.width Γ q.val z) = ∑ T : tilesAt Γ p z, pointWidth T.val z := by
  calc
    _ = ∑ T : tilesAt Γ p z, DirichletCornerAngles.width Γ (center Γ p z T) z :=
      ((equiv Γ p z).sum_comp (fun q : centersAt Γ p z => DirichletCornerAngles.width Γ q.val z)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      exact (tile_pointWidth_center Γ p z T).symm

end VeechDichotomy.TileCenterEquivalence
