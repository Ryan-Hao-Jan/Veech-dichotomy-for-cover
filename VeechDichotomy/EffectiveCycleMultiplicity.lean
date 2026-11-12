module

public import VeechDichotomy.TileCenterEquivalence

/-! The actual nearest-center angular sum equals the actual effective
stabilizer order times the actual congruence-cycle angular sum. This
unconditional identity proves the genuine multiplicity reduction; it
does not assume or assert that the nearest-center sum is already 2*pi. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.EffectiveCycleMultiplicity

open LinearGroup HyperbolicRegularCenters DirichletTileCenters EffectiveDirichletTiles
open EffectivePointStabilizers EffectiveCycleSums TileCenterEquivalence
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem center_width_sum (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) :
    (∑ q : centersAt Γ p z, DirichletCornerAngles.width Γ q.val z) =
      (effectiveOrder Γ z : ℝ) * ∑ w : cycle Γ p z, DirichletCornerAngles.width Γ p w.val := by
  rw [width_sum_centers_eq_tiles Γ p z]
  exact tile_width_sum Γ p hp z

theorem cycle_width_sum_eq_div (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) :
    (∑ w : cycle Γ p z, DirichletCornerAngles.width Γ p w.val) =
      (∑ q : centersAt Γ p z, DirichletCornerAngles.width Γ q.val z) / (effectiveOrder Γ z : ℝ) := by
  have hm : (effectiveOrder Γ z : ℝ) ≠ 0 := by exact_mod_cast (effectiveOrder_pos Γ z).ne'
  apply (eq_div_iff hm).mpr
  simpa only [mul_comm] using (center_width_sum Γ p hp z).symm

theorem tile_card (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) :
    Fintype.card (tilesAt Γ p z) = effectiveOrder Γ z * Fintype.card (cycle Γ p z) := by
  have h := weighted_sum Γ p hp z (fun _ : ℍ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

theorem center_card (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) :
    Fintype.card (centersAt Γ p z) = effectiveOrder Γ z * Fintype.card (cycle Γ p z) := by
  rw [← Fintype.card_congr (TileCenterEquivalence.equiv Γ p z)]
  exact tile_card Γ p hp z

theorem cycle_card_pos (p z : ℍ) : 0 < Fintype.card (cycle Γ p z) := Fintype.card_pos

end VeechDichotomy.EffectiveCycleMultiplicity
