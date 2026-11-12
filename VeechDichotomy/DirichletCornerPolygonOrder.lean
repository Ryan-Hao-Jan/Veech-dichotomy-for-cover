module

public import VeechDichotomy.DirichletCornerExposure

/-! Actual Dirichlet corners ordered by their Klein rays automatically
have the full strict convex polygon ordering. A wrongly oriented triple
would put its middle corner inside the actual triangle of the root and
two other corners, contradicting the proved exposed-corner property.
Consequently the native lattice supplies the actual exterior budget with
no extra supporting-edge or strict-chain hypothesis. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletCornerPolygonOrder

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions HyperbolicDirichletCorners
open HyperbolicKleinMap HyperbolicPolygonFans StrictKleinPolygons ComplexOrientedTriangles
open HyperbolicPolygonAreaAngle
open scoped UpperHalfPlane ENNReal

theorem positiveTriples (Γ : Subgroup SL2) (p a : ℍ) (v : ℕ → ℍ) (n : ℕ)
    (ha : a ∈ region Γ p) (hv : ∀ i : ℕ, i ≤ n → v i ∈ corners Γ p) (horder : OrderedRays a v n) :
    PositiveTriples v n := by
  intro i j k hij hjk hk
  have hj : j ≤ n := hjk.le.trans hk
  have hi : i ≤ n := hij.le.trans hj
  have hdistinct₁ := ordered_distinct horder hij hj
  have hdistinct₂ := ordered_distinct horder hjk hk
  have hmem (z : ℍ) (hz : z ∈ region Γ p) (hne : z ≠ v j) :
      point z ∈ point '' (region Γ p \ {v j}) :=
    ⟨z, ⟨hz, by simpa only [mem_singleton_iff] using hne⟩, rfl⟩
  have hsub : ({point a, point (v i), point (v k)} : Set ℂ) ⊆ point '' (region Γ p \ {v j}) := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hmem a ha hdistinct₁.2.1, hmem (v i) (hv i hi).1 hdistinct₁.2.2,
      hmem (v k) (hv k hk).1 hdistinct₂.2.2.symm⟩
  by_contra hnon
  have hnonpos : orient (point (v i)) (point (v j)) (point (v k)) ≤ 0 := le_of_not_gt hnon
  have hmiddle : 0 ≤ orient (point (v i)) (point (v k)) (point (v j)) := by
    rw [orient_swap (point (v i)) (point (v k)) (point (v j)),
      orient_rotate (point (v k)) (point (v i)) (point (v j))]
    exact neg_nonneg.mpr hnonpos
  have hlast : 0 ≤ orient (point (v k)) (point a) (point (v j)) := by
    rw [orient_rotate]
    exact (horder j k hjk hk).le
  have htri : point (v j) ∈ OrientedTriangleRegions.region (point a) (point (v i)) (point (v k)) :=
    (OrientedTriangleRegions.mem_iff _ _ _ _ (horder i k (hij.trans hjk) hk)).mpr
      ⟨(horder i j hij hj).le, hmiddle, hlast⟩
  exact DirichletCornerExposure.not_mem_hull_rest Γ p (v j) (hv j hj) (convexHull_mono hsub htri)

theorem strictlyOrdered (Γ : Subgroup SL2) (p a : ℍ) (v : ℕ → ℍ) (n : ℕ)
    (ha : a ∈ region Γ p) (hv : ∀ i : ℕ, i ≤ n → v i ∈ corners Γ p) (horder : OrderedRays a v n) :
    StrictlyOrdered a v n :=
  ⟨horder, positiveTriples Γ p a v n ha hv horder⟩

theorem exterior_bound (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p a : ℍ) (v : ℕ → ℍ) (n : ℕ)
    (hn : 0 < n) (ha : a ∈ region Γ p) (hv : ∀ i : ℕ, i ≤ n → v i ∈ corners Γ p)
    (horder : OrderedRays a v n) : exteriorSum a v n ≤ (volume (region Γ p)).toReal + 2 * Real.pi :=
  NativeDirichletPolygonDeficit.exterior_bound Γ hΓ p a v n hn (strictlyOrdered Γ p a v n ha hv horder)
    ha (fun i hi => (hv i hi).1)

end VeechDichotomy.DirichletCornerPolygonOrder
