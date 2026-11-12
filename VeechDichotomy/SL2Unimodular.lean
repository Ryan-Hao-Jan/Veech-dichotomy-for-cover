module

public import VeechDichotomy.NativeLatticeQuotient
public import VeechDichotomy.SL2Borel
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.GroupTheory.Abelianization.Defs

/-! Actual Haar measures on SL2(R) are also right invariant. The proved
elementary-matrix commutator theorem makes every homomorphism from SL2(R)
to a commutative monoid trivial, including its actual modular character.
This supplies unimodularity without a Lie-group classification axiom. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2Unimodular

open LinearGroup MeasureTheory

theorem commutator_eq_top : commutator SL2 = ⊤ :=
  Matrix.SL2.commutator_eq_top (a := (2 : ℝ)) (by norm_num) (by norm_num)

theorem hom_eq_one {M : Type*} [CommMonoid M] (f : SL2 →* M) (g : SL2) : f g = 1 := by
  have hg : g ∈ commutator SL2 := by rw [commutator_eq_top]; trivial
  have he : f.toHomUnits g = 1 := Abelianization.commutator_subset_ker f.toHomUnits hg
  exact congrArg Units.val he

theorem modularCharacter_eq_one (g : SL2) : Measure.modularCharacterFun g = 1 :=
  hom_eq_one Measure.modularCharacter g

instance haar_rightInvariant (ν : Measure SL2) [Measure.IsHaarMeasure ν] : ν.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul ν g, modularCharacter_eq_one, one_smul]

end VeechDichotomy.SL2Unimodular
