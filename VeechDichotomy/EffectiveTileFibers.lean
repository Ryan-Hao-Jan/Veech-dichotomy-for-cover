module

public import VeechDichotomy.EffectiveStabilizerTiles

/-! Every actual fiber of the tile-to-point-cycle map is a torsor for
the actual effective point stabilizer. The explicit relative element
between two tile representatives fixes the point and sends one entire
actual tile to the other. A genuine equivalence proves constant fiber
cardinality, with the ineffective kernel counted only once. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.EffectiveTileFibers

open LinearGroup Set HyperbolicRegularCenters HyperbolicDirichletTessellation HyperbolicDirichletRegions
open EffectiveDirichletTiles EffectivePointStabilizers EffectiveStabilizerTiles
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def fiber (Γ : Subgroup SL2) (p z w : ℍ) : Set (tilesAt Γ p z) := {T | cyclePoint Γ p z T = w}

theorem same_cyclePoint_transitive (Γ : Subgroup SL2) (p z : ℍ) (T U : tilesAt Γ p z)
    (he : cyclePoint Γ p z U = cyclePoint Γ p z T) :
    ∃ f : elements Γ z, moveTile Γ p z f T = U := by
  let δ := tileLabel Γ p z T
  let η := tileLabel Γ p z U
  have hpoints : η⁻¹ • z = δ⁻¹ • z := he
  have hfix : (η * δ⁻¹) • z = z := by
    rw [mul_smul, ← hpoints, smul_inv_smul]
  let f : elements Γ z := ⟨action Γ (η * δ⁻¹), η * δ⁻¹, hfix, rfl⟩
  refine ⟨f, ?_⟩
  apply Subtype.ext
  change (fun w : ℍ => (η * δ⁻¹) • w) '' T.val = U.val
  rw [← representative_tile Γ p z T, image_tile]
  change tile Γ p ((η * δ⁻¹) * δ) = U.val
  rw [mul_assoc, inv_mul_cancel, mul_one]
  exact representative_tile Γ p z U

def orbitMap (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (T : tilesAt Γ p z)
    (f : elements Γ z) : fiber Γ p z (cyclePoint Γ p z T) :=
  ⟨moveTile Γ p z f T, moveTile_cyclePoint Γ p hp z f T⟩

theorem orbitMap_bijective (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (T : tilesAt Γ p z) :
    Function.Bijective (orbitMap Γ p hp z T) := by
  constructor
  · intro f g he
    apply moveTile_injective Γ p hp z T
    exact congrArg Subtype.val he
  · intro U
    obtain ⟨f, hf⟩ := same_cyclePoint_transitive Γ p z T U.val U.property
    exact ⟨f, Subtype.ext hf⟩

def fiberEquiv (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (T : tilesAt Γ p z) :
    elements Γ z ≃ fiber Γ p z (cyclePoint Γ p z T) :=
  Equiv.ofBijective (orbitMap Γ p hp z T) (orbitMap_bijective Γ p hp z T)

theorem fiber_card_of_tile (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (T : tilesAt Γ p z) :
    Nat.card (fiber Γ p z (cyclePoint Γ p z T)) = effectiveOrder Γ z :=
  (Nat.card_congr (fiberEquiv Γ p hp z T)).symm

theorem fiber_card (Γ : Subgroup SL2) (p : ℍ) (hp : RegularCenter Γ p) (z w : ℍ)
    (hw : w ∈ region Γ p ∩ MulAction.orbit Γ z) : Nat.card (fiber Γ p z w) = effectiveOrder Γ z := by
  have hrange : w ∈ range (cyclePoint Γ p z) := by rw [range_cyclePoint Γ p hp z]; exact hw
  obtain ⟨T, hT⟩ := hrange
  rw [← hT]
  exact fiber_card_of_tile Γ p hp z T

end VeechDichotomy.EffectiveTileFibers
