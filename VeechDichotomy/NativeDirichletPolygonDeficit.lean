module

public import VeechDichotomy.HyperbolicPolygonAreaAngle
public import VeechDichotomy.NativeLatticeDirichletArea

/-! The actual native SL2 lattice hypothesis bounds the total exterior
angle deficit of every strictly ordered finite polygon in its actual
Dirichlet region. Genuine geodesic convexity and the already proved
finite actual area discharge all geometric measure hypotheses. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDirichletPolygonDeficit

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions
open HyperbolicGeodesicHulls HyperbolicPolygonFans StrictKleinPolygons
open HyperbolicPolygonAreaAngle
open scoped UpperHalfPlane ENNReal

theorem dirichlet_geodesicallyConvex (Γ : Subgroup SL2) (p : ℍ) : GeodesicallyConvex (region Γ p) := by
  intro a ha b hb
  exact HyperbolicCanonicalSegments.metricSegment_subset_region Γ p a b ha hb

theorem exterior_bound (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p a : ℍ) (v : ℕ → ℍ) (n : ℕ)
    (hn : 0 < n) (h : StrictlyOrdered a v n) (ha : a ∈ region Γ p)
    (hv : ∀ i : ℕ, i ≤ n → v i ∈ region Γ p) :
    exteriorSum a v n ≤ (volume (region Γ p)).toReal + 2 * Real.pi :=
  HyperbolicPolygonAreaAngle.exterior_bound (region Γ p) (dirichlet_geodesicallyConvex Γ p)
    (NativeLatticeDirichletArea.area_lt_top Γ hΓ p).ne a v n hn h ha hv

theorem polygon_subset_dirichlet (Γ : Subgroup SL2) (p a : ℍ) (v : ℕ → ℍ) (n : ℕ)
    (ha : a ∈ region Γ p) (hv : ∀ i : ℕ, i ≤ n → v i ∈ region Γ p) :
    polygon a v n ⊆ region Γ p :=
  HyperbolicFanAreas.polygon_subset (dirichlet_geodesicallyConvex Γ p) a v n ha hv

end VeechDichotomy.NativeDirichletPolygonDeficit
