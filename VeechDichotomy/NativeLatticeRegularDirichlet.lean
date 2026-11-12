module

public import VeechDichotomy.NativeLatticeDirichletArea
public import VeechDichotomy.HyperbolicRegularCenters

/-! The native lattice hypothesis supplies an actual regular center and
its actual positive finite-area Dirichlet region with null boundary.
The center is chosen by the proved countable fixed-set nullness argument;
its stabilizer consists entirely of maps acting trivially on the plane. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeRegularDirichlet

open LinearGroup NativeVeech HyperbolicRegularCenters HyperbolicDirichletRegions MeasureTheory
open scoped UpperHalfPlane ENNReal

theorem exists_regular_dirichlet (Γ : Subgroup SL2) (hΓ : IsLattice Γ) :
    ∃ p : ℍ, RegularCenter Γ p ∧ MeasurableSet (region Γ p) ∧ 0 < volume (region Γ p) ∧
      volume (region Γ p) < ∞ ∧ volume (frontier (region Γ p)) = 0 := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  obtain ⟨p, hp⟩ := HyperbolicRegularCenters.exists_regular_center Γ
  exact ⟨p, hp, NativeLatticeDirichletArea.dirichlet_region_finite_area Γ hΓ p⟩

end VeechDichotomy.NativeLatticeRegularDirichlet
