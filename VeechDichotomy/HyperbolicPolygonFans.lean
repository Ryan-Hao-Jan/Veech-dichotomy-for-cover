module

public import VeechDichotomy.PlanarFanIntersections

/-! Literal hyperbolic polygon fan regions and their entire triangulation.
The actual Klein homeomorphism transfers the proved determinant conditions
and triangle union. Distinct actual triangles meet only on an actual
metric diagonal, which has zero actual hyperbolic area. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicPolygonFans

open Set MeasureTheory HyperbolicGeodesicHulls HyperbolicKleinMap HyperbolicTriangles HyperbolicMetricSegments
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def vertices (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : Set ℍ := insert a (v '' Iic n)
def polygon (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : Set ℍ := hull (vertices a v n)

def OrderedRays (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : Prop :=
  OrderedPlanarFans.OrderedRays (point a) (fun i => point (v i)) n

def SupportingEdges (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : Prop :=
  OrderedPlanarFans.SupportingEdges (point a) (fun i => point (v i)) n

theorem image_vertices (a : ℍ) (v : ℕ → ℍ) (n : ℕ) :
    point '' vertices a v n = OrderedPlanarFans.vertices (point a) (fun i => point (v i)) n := by
  simp only [vertices, OrderedPlanarFans.vertices, image_insert_eq, image_image]

theorem polygon_mem_iff (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (z : ℍ) :
    z ∈ polygon a v n ↔ point z ∈ OrderedPlanarFans.polygon (point a) (fun i => point (v i)) n := by
  change point z ∈ convexHull ℝ (point '' vertices a v n) ↔ _
  rw [image_vertices]
  rfl

theorem triangle_mem_iff (a b c z : ℍ) :
    z ∈ triangle a b c ↔ point z ∈ OrientedTriangleRegions.region (point a) (point b) (point c) := by
  change point z ∈ convexHull ℝ (point '' {a, b, c}) ↔ _
  rw [image_insert_eq, image_insert_eq, image_singleton]
  rfl

theorem isCompact_polygon (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : IsCompact (polygon a v n) :=
  isCompact_hull (((Set.finite_Iic n).image v).insert a)

theorem measurableSet_polygon (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : MeasurableSet (polygon a v n) :=
  (isCompact_polygon a v n).isClosed.measurableSet

theorem area_polygon_lt_top (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : volume (polygon a v n) < ⊤ :=
  (isCompact_polygon a v n).measure_lt_top

theorem triangle_subset_polygon (a : ℍ) (v : ℕ → ℍ) (n i : ℕ) (hi : i < n) :
    triangle a (v i) (v (i + 1)) ⊆ polygon a v n := by
  intro z hz
  rw [polygon_mem_iff]
  exact OrderedPlanarFans.triangle_subset_polygon (point a) (fun j => point (v j)) n i hi
    ((triangle_mem_iff a (v i) (v (i + 1)) z).mp hz)

theorem polygon_eq_fan (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n)
    (horder : OrderedRays a v n) (hedge : SupportingEdges a v n) :
    polygon a v n = ⋃ i ∈ Finset.range n, triangle a (v i) (v (i + 1)) := by
  ext z
  rw [polygon_mem_iff, OrderedPlanarFans.polygon_eq_fan _ _ n hn horder hedge]
  simp only [mem_iUnion, exists_prop, ← triangle_mem_iff]

theorem intersection_subset_diagonal (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (horder : OrderedRays a v n)
    {i j : ℕ} (hij : i < j) (hj : j < n) :
    triangle a (v i) (v (i + 1)) ∩ triangle a (v j) (v (j + 1)) ⊆ metricSegment a (v (i + 1)) := by
  intro z hz
  rw [HyperbolicKleinGeodesics.mem_metricSegment_iff]
  exact PlanarFanIntersections.intersection_subset_diagonal (point a) (fun k => point (v k)) n horder hij hj
    ⟨(triangle_mem_iff _ _ _ z).mp hz.1, (triangle_mem_iff _ _ _ z).mp hz.2⟩

theorem intersection_null (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (horder : OrderedRays a v n)
    {i j : ℕ} (hij : i < j) (hj : j < n) :
    volume (triangle a (v i) (v (i + 1)) ∩ triangle a (v j) (v (j + 1))) = 0 :=
  measure_mono_null (intersection_subset_diagonal a v n horder hij hj) (metricSegment_null _ _)

end VeechDichotomy.HyperbolicPolygonFans
