module

public import VeechDichotomy.DirichletExtremePoints
public import Mathlib.Analysis.Convex.KreinMilman

/-! The entire actual closed Klein Dirichlet region of a native lattice
at a regular center is the convex hull of its finitely many actual true
corners and actual ideal endpoints. Compact convexity and the proved
classification of extreme points discharge the geometric hull statement. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDirichletFiniteHull

open LinearGroup NativeVeech Set HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicKleinMap DirichletKleinClosure DirichletExtremePoints
open scoped UpperHalfPlane

theorem vertices_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    (vertices Γ p).Finite :=
  ((NativeDirichletFiniteCorners.corners_finite Γ hΓ p hp).image point).union
    (NativeDirichletFiniteIdealBoundary.idealBoundary_finite Γ hΓ p)

theorem eq_convexHull_of_finite (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ)
    (hf : (vertices Γ p).Finite) : closedRegion Γ p = convexHull ℝ (vertices Γ p) := by
  apply Subset.antisymm
  · calc
      _ = closure (convexHull ℝ ((closedRegion Γ p).extremePoints ℝ)) :=
        (closure_convexHull_extremePoints (isCompact_closedRegion Γ p) (convex_closedRegion Γ p)).symm
      _ ⊆ closure (convexHull ℝ (vertices Γ p)) :=
        closure_mono (convexHull_mono (extremePoints_subset_vertices Γ p))
      _ = _ := (hf.isCompact_convexHull ℝ).isClosed.closure_eq
  · exact convexHull_min (vertices_subset Γ p) (convex_closedRegion Γ p)

theorem closedRegion_eq_convexHull (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ)
    (hp : RegularCenter Γ p) : closedRegion Γ p = convexHull ℝ (vertices Γ p) := by
  let : DiscreteTopology Γ := hΓ.1
  exact eq_convexHull_of_finite Γ p (vertices_finite Γ hΓ p hp)

theorem image_region_eq (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    point '' region Γ p = convexHull ℝ (vertices Γ p) ∩ Metric.ball 0 1 := by
  rw [DirichletKleinClosure.image_region_eq, closedRegion_eq_convexHull Γ hΓ p hp]

theorem exists_finite_hull (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    ∃ V : Finset ℂ, (V : Set ℂ) = vertices Γ p ∧ closedRegion Γ p = convexHull ℝ (V : Set ℂ) := by
  classical
  let V := (vertices_finite Γ hΓ p hp).toFinset
  have hV : (V : Set ℂ) = vertices Γ p := Set.Finite.coe_toFinset _
  exact ⟨V, hV, hV ▸ closedRegion_eq_convexHull Γ hΓ p hp⟩

end VeechDichotomy.NativeDirichletFiniteHull
