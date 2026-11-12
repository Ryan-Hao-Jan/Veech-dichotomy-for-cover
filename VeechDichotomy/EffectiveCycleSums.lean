module

public import VeechDichotomy.EffectiveTileFibers
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual finite summation over the tile-to-point-cycle fibers.
The proved effective-stabilizer equivalences give the exact common
cardinality, so every actual weighted tile sum is the effective order
times the corresponding actual point-cycle sum. No angular-sum
identity is assumed in this counting theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.EffectiveCycleSums

open LinearGroup Set HyperbolicDirichletRegions HyperbolicRegularCenters HyperbolicDirichletPointCycles
open EffectiveDirichletTiles EffectivePointStabilizers EffectiveTileFibers HyperbolicRegionAngles
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

abbrev cycle (Γ : Subgroup SL2) (p z : ℍ) : Set ℍ := region Γ p ∩ MulAction.orbit Γ z

noncomputable instance tilesFintype (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : Fintype (tilesAt Γ p z) :=
  (tilesAt_finite Γ p z).fintype

noncomputable instance cycleFintype (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : Fintype (cycle Γ p z) :=
  (cycle_finite Γ p z).fintype

instance cycleNonempty (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : Nonempty (cycle Γ p z) := by
  obtain ⟨γ, hγ⟩ := exists_translate_mem Γ p z
  exact ⟨⟨γ • z, hγ, MulAction.mem_orbit z γ⟩⟩

def cycleMap (Γ : Subgroup SL2) (p z : ℍ) (T : tilesAt Γ p z) : cycle Γ p z :=
  ⟨cyclePoint Γ p z T, cyclePoint_mem_cycle Γ p z T⟩

def cycleFiberEquiv (Γ : Subgroup SL2) (p z : ℍ) (w : cycle Γ p z) :
    {T : tilesAt Γ p z // cycleMap Γ p z T = w} ≃ fiber Γ p z w.val where
  toFun T := ⟨T.val, congrArg Subtype.val T.property⟩
  invFun T := ⟨T.val, Subtype.ext T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance mapFiberFintype (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) (w : cycle Γ p z) :
    Fintype {T : tilesAt Γ p z // cycleMap Γ p z T = w} := by
  classical
  exact Subtype.fintype (fun T : tilesAt Γ p z => cycleMap Γ p z T = w)

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem card_map_fiber (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (w : cycle Γ p z) :
    Fintype.card {T : tilesAt Γ p z // cycleMap Γ p z T = w} = effectiveOrder Γ z := by
  classical
  have hn : Nat.card {T : tilesAt Γ p z // cycleMap Γ p z T = w} = effectiveOrder Γ z :=
    (Nat.card_congr (cycleFiberEquiv Γ p z w)).trans (fiber_card Γ p hp z w.val w.property)
  simpa only [Nat.card_eq_fintype_card] using hn

theorem weighted_sum (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (F : ℍ → ℝ) :
    (∑ T : tilesAt Γ p z, F (cyclePoint Γ p z T)) =
      (effectiveOrder Γ z : ℝ) * ∑ w : cycle Γ p z, F w.val := by
  classical
  have hsum := Fintype.sum_fiberwise' (cycleMap Γ p z) (fun w : cycle Γ p z => F w.val)
  calc
    _ = ∑ w : cycle Γ p z, ∑ _T : {T : tilesAt Γ p z // cycleMap Γ p z T = w}, F w.val := hsum.symm
    _ = ∑ w : cycle Γ p z, (effectiveOrder Γ z : ℝ) * F w.val := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_map_fiber Γ p hp z w]
    _ = _ := by rw [Finset.mul_sum]

theorem tile_width_sum (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) :
    (∑ T : tilesAt Γ p z, pointWidth T.val z) =
      (effectiveOrder Γ z : ℝ) * ∑ w : cycle Γ p z, DirichletCornerAngles.width Γ p w.val := by
  calc
    _ = ∑ T : tilesAt Γ p z, DirichletCornerAngles.width Γ p (cyclePoint Γ p z T) := by
      apply Finset.sum_congr rfl
      intro T _
      exact tile_pointWidth Γ p z T
    _ = _ := weighted_sum Γ p hp z (DirichletCornerAngles.width Γ p)

end VeechDichotomy.EffectiveCycleSums
