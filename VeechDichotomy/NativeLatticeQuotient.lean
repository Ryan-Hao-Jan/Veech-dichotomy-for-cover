module

public import VeechDichotomy.NativeVeech
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-! The actual quotient attached to the native lattice hypothesis is
Hausdorff, locally compact and second countable. Its invariant probability
measure is chosen from the hypothesis with its stated properties proved.
No directional-return or cusp theorem is part of this construction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeQuotient

open LinearGroup NativeVeech Set Topology MeasureTheory

instance secondCountableSL2 : SecondCountableTopology SL2 := by
  let : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

instance quotientBorelSpace (Γ : Subgroup SL2) : BorelSpace (SL2 ⧸ Γ) := ⟨rfl⟩

theorem subgroup_closed (Γ : Subgroup SL2) (hΓ : IsLattice Γ) : IsClosed (Γ : Set SL2) := by
  let : DiscreteTopology Γ := hΓ.1
  exact Subgroup.isClosed_of_discreteTopology

theorem quotient_t2Space (Γ : Subgroup SL2) (hΓ : IsLattice Γ) : T2Space (SL2 ⧸ Γ) := by
  let : IsClosed (Γ : Set SL2) := subgroup_closed Γ hΓ
  infer_instance

theorem quotient_secondCountable (Γ : Subgroup SL2) : SecondCountableTopology (SL2 ⧸ Γ) := inferInstance

theorem quotient_locallyCompact (Γ : Subgroup SL2) : LocallyCompactSpace (SL2 ⧸ Γ) := inferInstance

theorem quotient_sigmaCompact (Γ : Subgroup SL2) (hΓ : IsLattice Γ) : SigmaCompactSpace (SL2 ⧸ Γ) := by
  let : T2Space (SL2 ⧸ Γ) := quotient_t2Space Γ hΓ
  infer_instance

def invariantMeasure (Γ : Subgroup SL2) (hΓ : IsLattice Γ) : Measure (SL2 ⧸ Γ) := Classical.choose hΓ.2

instance invariantMeasure_probability (Γ : Subgroup SL2) (hΓ : IsLattice Γ) :
    IsProbabilityMeasure (invariantMeasure Γ hΓ) := (Classical.choose_spec hΓ.2).1

instance invariantMeasure_invariant (Γ : Subgroup SL2) (hΓ : IsLattice Γ) :
    SMulInvariantMeasure SL2 (SL2 ⧸ Γ) (invariantMeasure Γ hΓ) := (Classical.choose_spec hΓ.2).2

end VeechDichotomy.NativeLatticeQuotient
