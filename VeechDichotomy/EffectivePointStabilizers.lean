module

public import VeechDichotomy.DirichletRegionDeficitBudgets
public import Mathlib.SetTheory.Cardinal.Finite

/-! The actual effective stabilizer at a point is the finite set of
global action functions of its genuine stabilizer elements. Equal
functions are counted once, so the ineffective SL2 kernel is retained
without assuming faithfulness. Its actual order is a positive integer. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.EffectivePointStabilizers

open LinearGroup Set
open scoped UpperHalfPlane

def action (Γ : Subgroup SL2) (γ : Γ) : ℍ → ℍ := fun w => γ • w

def elements (Γ : Subgroup SL2) (z : ℍ) : Set (ℍ → ℍ) := action Γ '' {γ : Γ | γ • z = z}

def representative (Γ : Subgroup SL2) (z : ℍ) (f : elements Γ z) : Γ := Classical.choose f.property

theorem representative_fixes (Γ : Subgroup SL2) (z : ℍ) (f : elements Γ z) :
    representative Γ z f • z = z := (Classical.choose_spec f.property).1

theorem representative_action (Γ : Subgroup SL2) (z : ℍ) (f : elements Γ z) :
    action Γ (representative Γ z f) = f.val := (Classical.choose_spec f.property).2

theorem representative_apply (Γ : Subgroup SL2) (z : ℍ) (f : elements Γ z) (w : ℍ) :
    representative Γ z f • w = f.val w := congrFun (representative_action Γ z f) w

theorem apply_fixed (Γ : Subgroup SL2) (z : ℍ) (f : elements Γ z) : f.val z = z := by
  rw [← representative_apply, representative_fixes]

theorem identity_mem (Γ : Subgroup SL2) (z : ℍ) : (fun w : ℍ => w) ∈ elements Γ z := by
  refine ⟨1, one_smul Γ z, ?_⟩
  funext w
  exact one_smul Γ w

theorem elements_nonempty (Γ : Subgroup SL2) (z : ℍ) : (elements Γ z).Nonempty :=
  ⟨fun w => w, identity_mem Γ z⟩

theorem elements_finite (Γ : Subgroup SL2) [DiscreteTopology Γ] (z : ℍ) : (elements Γ z).Finite :=
  (HyperbolicStrictDirichlet.stabilizer_finite Γ z).image (action Γ)

def effectiveOrder (Γ : Subgroup SL2) (z : ℍ) : ℕ := Nat.card (elements Γ z)

theorem effectiveOrder_pos (Γ : Subgroup SL2) [DiscreteTopology Γ] (z : ℍ) : 0 < effectiveOrder Γ z := by
  let : Finite (elements Γ z) := (elements_finite Γ z).to_subtype
  let : Nonempty (elements Γ z) := ⟨⟨fun w => w, identity_mem Γ z⟩⟩
  exact Nat.card_pos

end VeechDichotomy.EffectivePointStabilizers
