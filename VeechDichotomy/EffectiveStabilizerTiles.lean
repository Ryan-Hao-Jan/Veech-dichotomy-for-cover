module

public import VeechDichotomy.EffectivePointStabilizers

/-! The actual effective point stabilizer acts on actual distinct
tiles at that point. It preserves the actual point-cycle preimage,
and at a regular center its action on a fixed tile is injective.
All maps use genuine group representatives with choice independence
controlled by the already proved equality of global actions. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.EffectiveStabilizerTiles

open LinearGroup Set HyperbolicDirichletTessellation HyperbolicRegularCenters
open EffectiveDirichletTiles EffectivePointStabilizers
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

abbrev stabilizerLabel (Γ : Subgroup SL2) (z : ℍ) (f : elements Γ z) : Γ :=
  EffectivePointStabilizers.representative Γ z f

abbrev tileLabel (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : Γ :=
  EffectiveDirichletTiles.representative Γ p z T

theorem image_eq_tile (Γ : Subgroup SL2) (p z : ℍ) (f : elements Γ z) (T : tilesAt Γ p z) :
    f.val '' T.val = tile Γ p (stabilizerLabel Γ z f * tileLabel Γ p z T) := by
  rw [← representative_action Γ z f, ← representative_tile Γ p z T]
  exact image_tile Γ p _ _

def moveTile (Γ : Subgroup SL2) (p z : ℍ) (f : elements Γ z) (T : tilesAt Γ p z) : tilesAt Γ p z := by
  refine ⟨f.val '' T.val, ?_⟩
  have hzT : z ∈ T.val := by rw [← representative_tile Γ p z T]; exact representative_mem Γ p z T
  refine ⟨stabilizerLabel Γ z f * tileLabel Γ p z T, ?_, (image_eq_tile Γ p z f T).symm⟩
  change z ∈ tile Γ p (stabilizerLabel Γ z f * tileLabel Γ p z T)
  rw [← image_eq_tile Γ p z f T]
  exact ⟨z, hzT, apply_fixed Γ z f⟩

theorem moveTile_label (Γ : Subgroup SL2) (p z : ℍ) (f : elements Γ z) (T : tilesAt Γ p z) :
    tile Γ p (stabilizerLabel Γ z f * tileLabel Γ p z T) = (moveTile Γ p z f T).val :=
  (image_eq_tile Γ p z f T).symm

theorem moveTile_cyclePoint (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ)
    (f : elements Γ z) (T : tilesAt Γ p z) : cyclePoint Γ p z (moveTile Γ p z f T) = cyclePoint Γ p z T := by
  rw [cyclePoint_eq_of_label Γ p hp z (moveTile Γ p z f T) _ (moveTile_label Γ p z f T)]
  change (stabilizerLabel Γ z f * tileLabel Γ p z T)⁻¹ • z = (tileLabel Γ p z T)⁻¹ • z
  rw [mul_inv_rev, mul_smul]
  have hinv : (stabilizerLabel Γ z f)⁻¹ • z = z := by
    have he := congrArg (fun w : ℍ => (stabilizerLabel Γ z f)⁻¹ • w) (representative_fixes Γ z f)
    simpa only [inv_smul_smul] using he.symm
  rw [hinv]

theorem moveTile_injective (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (T : tilesAt Γ p z) :
    Function.Injective (fun f : elements Γ z => moveTile Γ p z f T) := by
  intro f g he
  have htiles : tile Γ p (stabilizerLabel Γ z f * tileLabel Γ p z T) =
      tile Γ p (stabilizerLabel Γ z g * tileLabel Γ p z T) :=
    (moveTile_label Γ p z f T).trans ((congrArg Subtype.val he).trans (moveTile_label Γ p z g T).symm)
  have hactions := (tile_eq_iff_actions_eq Γ p hp _ _).mp htiles
  apply Subtype.ext
  funext w
  have h := hactions ((tileLabel Γ p z T)⁻¹ • w)
  simp only [mul_smul, smul_inv_smul] at h
  simpa only [representative_apply] using h

end VeechDichotomy.EffectiveStabilizerTiles
