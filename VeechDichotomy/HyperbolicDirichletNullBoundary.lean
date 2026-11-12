module

public import VeechDichotomy.HyperbolicBisectorNull
public import VeechDichotomy.HyperbolicStrictDirichlet

/-! The genuine Dirichlet region differs from its strict region by a
hyperbolic null set. Countably many actual distinct-center bisectors
contain the difference; for a discrete subgroup they also contain the
whole actual frontier. Finite stabilizers remain allowed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletNullBoundary

open LinearGroup HyperbolicDirichletRegions HyperbolicStrictDirichlet
open HyperbolicBisectorNull Set MeasureTheory
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2) [Countable Γ]

def walls (p : ℍ) : Set ℍ := ⋃ γ : {γ : Γ | γ • p ≠ p}, bisector p (γ.val • p)

theorem walls_null (p : ℍ) : volume (walls Γ p) = 0 :=
  measure_iUnion_null (fun γ => volume_bisector γ.property.symm)

omit [Countable Γ] in
theorem difference_subset_walls (p : ℍ) : region Γ p \ strictRegion Γ p ⊆ walls Γ p := by
  classical
  intro z hz
  have hn : ¬ ∀ γ : Γ, γ • p ≠ p → dist z p < dist z (γ • p) := hz.2
  obtain ⟨γ, hγ⟩ := not_forall.mp hn
  obtain ⟨hdistinct, hnotlt⟩ := not_imp.mp hγ
  have heq : dist z p = dist z (γ • p) := le_antisymm (hz.1 γ) (le_of_not_gt hnotlt)
  exact mem_iUnion.mpr ⟨⟨γ, hdistinct⟩, heq⟩

theorem difference_null (p : ℍ) : volume (region Γ p \ strictRegion Γ p) = 0 :=
  measure_mono_null (difference_subset_walls Γ p) (walls_null Γ p)

theorem volume_region_eq_strict (p : ℍ) : volume (region Γ p) = volume (strictRegion Γ p) := by
  apply le_antisymm _ (measure_mono (subset_region Γ p))
  calc
    volume (region Γ p) ≤ volume (strictRegion Γ p ∪ (region Γ p \ strictRegion Γ p)) := by
      apply measure_mono
      intro z hz
      by_cases hs : z ∈ strictRegion Γ p
      · exact Or.inl hs
      · exact Or.inr ⟨hz, hs⟩
    _ ≤ volume (strictRegion Γ p) + volume (region Γ p \ strictRegion Γ p) := measure_union_le _ _
    _ = volume (strictRegion Γ p) := by rw [difference_null, add_zero]

theorem frontier_null [DiscreteTopology Γ] (p : ℍ) : volume (frontier (region Γ p)) = 0 := by
  apply measure_mono_null (t := walls Γ p) _ (walls_null Γ p)
  intro z hz
  obtain ⟨γ, hdistinct, heq⟩ := HyperbolicDirichletLocalFiniteness.frontier_mem_bisector Γ p hz
  exact mem_iUnion.mpr ⟨⟨γ, hdistinct⟩, heq⟩

end VeechDichotomy.HyperbolicDirichletNullBoundary
