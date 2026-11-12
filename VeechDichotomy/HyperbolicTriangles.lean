module

public import VeechDichotomy.HyperbolicGeodesicHulls
public import Mathlib.Analysis.Convex.Join

/-! Finite triangles are literal intrinsic convex hulls of three actual
upper-half-plane vertices. They are compact measurable sets of finite
area, transport exactly under SL2, and are precisely the fans of actual
metric segments from any vertex to the opposite side. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicTriangles

open LinearGroup Set MeasureTheory HyperbolicMetricSegments HyperbolicGeodesicHulls
open HyperbolicKleinMap HyperbolicKleinGeodesics
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def triangle (a b c : ℍ) : Set ℍ := hull {a, b, c}

theorem image_triangle (a b c : ℍ) :
    point '' triangle a b c = convexHull ℝ {point a, point b, point c} := by
  simp only [triangle, image_hull, image_insert_eq, image_singleton]

theorem image_triangle_smul (A : SL2) (a b c : ℍ) :
    (fun z : ℍ => A • z) '' triangle a b c = triangle (A • a) (A • b) (A • c) := by
  simp only [triangle, image_hull_smul, image_insert_eq, image_singleton]

theorem geodesicallyConvex_triangle (a b c : ℍ) : GeodesicallyConvex (triangle a b c) :=
  geodesicallyConvex_hull _

theorem isCompact_triangle (a b c : ℍ) : IsCompact (triangle a b c) :=
  isCompact_hull (by simp)

theorem isClosed_triangle (a b c : ℍ) : IsClosed (triangle a b c) :=
  (isCompact_triangle a b c).isClosed

theorem measurableSet_triangle (a b c : ℍ) : MeasurableSet (triangle a b c) :=
  (isClosed_triangle a b c).measurableSet

theorem area_triangle_lt_top (a b c : ℍ) : volume (triangle a b c) < ⊤ :=
  (isCompact_triangle a b c).measure_lt_top

theorem first_mem (a b c : ℍ) : a ∈ triangle a b c := subset_hull _ (by simp)
theorem second_mem (a b c : ℍ) : b ∈ triangle a b c := subset_hull _ (by simp)
theorem third_mem (a b c : ℍ) : c ∈ triangle a b c := subset_hull _ (by simp)

theorem opposite_side_subset (a b c : ℍ) : metricSegment b c ⊆ triangle a b c :=
  geodesicallyConvex_triangle a b c (second_mem a b c) (third_mem a b c)

theorem mem_triangle_iff (a b c z : ℍ) :
    z ∈ triangle a b c ↔ ∃ q ∈ metricSegment b c, z ∈ metricSegment a q := by
  constructor
  · intro hz
    have hpz : point z ∈ convexHull ℝ {point a, point b, point c} := by
      rw [← image_triangle]
      exact ⟨z, hz, rfl⟩
    rw [← convexJoin_singleton_segment] at hpz
    obtain ⟨u, hu, v, hv, hpz⟩ := mem_convexJoin.mp hpz
    have hua : u = point a := hu
    subst u
    rw [← HyperbolicKleinGeodesics.image_metricSegment] at hv
    obtain ⟨q, hq, rfl⟩ := hv
    exact ⟨q, hq, (mem_metricSegment_iff a q z).mpr hpz⟩
  · rintro ⟨q, hq, hz⟩
    exact geodesicallyConvex_triangle a b c (first_mem a b c) (opposite_side_subset a b c hq) hz

theorem triangle_eq_fan (a b c : ℍ) :
    triangle a b c = ⋃ q ∈ metricSegment b c, metricSegment a q := by
  ext z
  simp only [mem_triangle_iff, mem_iUnion, exists_prop]

theorem triangle_subset {S : Set ℍ} (hS : GeodesicallyConvex S) {a b c : ℍ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : triangle a b c ⊆ S :=
  hull_min (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨ha, hb, hc⟩) hS

theorem isCompact_metricSegment (a b : ℍ) : IsCompact (metricSegment a b) := by
  rw [← hull_pair]
  exact isCompact_hull (by simp)

theorem metricSegment_null (a b : ℍ) : volume (metricSegment a b) = 0 := by
  obtain ⟨A, c, s, t, hs, ht⟩ := HyperbolicCommonGeodesic.exists_clock_coordinates a b
  change HyperbolicDirichletGeodesics.line A c s = a at hs
  change HyperbolicDirichletGeodesics.line A c t = b at ht
  let p := A⁻¹ • reflectionLeft c
  let q := A⁻¹ • reflectionRight c
  have hpq : p ≠ q := fun he => reflection_ne c ((MulAction.injective A⁻¹) he)
  apply measure_mono_null (t := HyperbolicBisectorNull.bisector p q) _
    (HyperbolicBisectorNull.volume_bisector hpq)
  rw [← hs, ← ht, metricSegment_eq_line_interval]
  rintro _ ⟨u, _, rfl⟩
  exact line_bisector A c u

def sides (a b c : ℍ) : Set ℍ := metricSegment a b ∪ metricSegment b c ∪ metricSegment c a

theorem sides_null (a b c : ℍ) : volume (sides a b c) = 0 :=
  measure_union_null (measure_union_null (metricSegment_null a b) (metricSegment_null b c))
    (metricSegment_null c a)

end VeechDichotomy.HyperbolicTriangles
