module

public import VeechDichotomy.NativeCornerOrbitFiniteness
public import VeechDichotomy.NativeLatticeRegularDirichlet

/-! A genuine native SL2 lattice has only finitely many actual true
corners in every regular-center Dirichlet region. The proved finite
number of corner orbit classes and actual finiteness of each point
cycle cover the entire actual corner set. Ideal ends and sides are
not asserted finite by this theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDirichletFiniteCorners

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions HyperbolicDirichletCorners
open HyperbolicRegularCenters HyperbolicDirichletPointCycles DirichletCornerOrbitCycles
open scoped UpperHalfPlane ENNReal

theorem corners_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    (corners Γ p).Finite := by
  let : DiscreteTopology Γ := hΓ.1
  classical
  have hclasses := NativeCornerOrbitFiniteness.cornerClasses_finite Γ hΓ p hp
  let : Finite (cornerClasses Γ p) := hclasses.to_subtype
  have hcycles : (⋃ q : cornerClasses Γ p, region Γ p ∩ MulAction.orbit Γ (selected Γ p q)).Finite :=
    Set.finite_iUnion (fun q => cycle_finite Γ p (selected Γ p q))
  apply hcycles.subset
  intro w hw
  let q : cornerClasses Γ p := ⟨classOf Γ w, w, hw, rfl⟩
  have horbit : w ∈ MulAction.orbit Γ (selected Γ p q) :=
    orbit_of_class_eq Γ w (selected Γ p q) (selected_class Γ p q).symm
  exact mem_iUnion.mpr ⟨q, hw.1, horbit⟩

theorem exists_regular_finite_corners (Γ : Subgroup SL2) (hΓ : IsLattice Γ) :
    ∃ p : ℍ, RegularCenter Γ p ∧ (corners Γ p).Finite ∧ MeasurableSet (region Γ p) ∧
      0 < volume (region Γ p) ∧ volume (region Γ p) < ∞ ∧ volume (frontier (region Γ p)) = 0 := by
  obtain ⟨p, hp, hm, hpos, hfin, hnull⟩ := NativeLatticeRegularDirichlet.exists_regular_dirichlet Γ hΓ
  exact ⟨p, hp, corners_finite Γ hΓ p hp, hm, hpos, hfin, hnull⟩

end VeechDichotomy.NativeDirichletFiniteCorners
