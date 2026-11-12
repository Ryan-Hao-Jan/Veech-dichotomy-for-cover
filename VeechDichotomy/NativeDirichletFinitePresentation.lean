module

public import VeechDichotomy.DirichletGlobalActiveLabels
public import VeechDichotomy.HyperbolicConstraintRegions

/-! A native lattice's actual regular-center Dirichlet region is
defined by finitely many genuine group distance inequalities. The finite
set is the actual set of labels whose bisectors touch the region, and
the genuine local active-constraint theorem proves global equality. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDirichletFinitePresentation

open LinearGroup NativeVeech Set HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicDirichletIncidence HyperbolicConstraintRegions DirichletActiveConstraints
open scoped UpperHalfPlane

theorem region_eq_active_constraints (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) :
    region Γ p = constraints Γ p (activeLabels Γ p (region Γ p)) := by
  apply eq_of_contains_active
  intro z hz γ hγ
  exact ⟨z, hz, hz, hγ.2⟩

theorem exists_finite_constraints (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    ∃ S : Finset Γ, region Γ p = {z : ℍ | ∀ γ ∈ S, dist z p ≤ dist z (γ • p)} := by
  let : DiscreteTopology Γ := hΓ.1
  classical
  let S := (DirichletGlobalActiveLabels.activeLabels_region_finite Γ hΓ p hp).toFinset
  refine ⟨S, ?_⟩
  rw [region_eq_active_constraints]
  ext z
  simp only [constraints, mem_ofPred_eq, Set.Finite.mem_toFinset, S]

end VeechDichotomy.NativeDirichletFinitePresentation
