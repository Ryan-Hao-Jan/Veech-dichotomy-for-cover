module

public import VeechDichotomy.HyperbolicPolygonFans

/-! Actual hyperbolic area additivity for the proved polygon fan.
Shared actual metric diagonals have zero area, so genuine almost-everywhere
disjointness supplies the finite measure sum. The actual finite-triangle
Gauss--Bonnet formula then gives the sum of actual triangle angle deficits. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicFanAreas

open Set MeasureTheory HyperbolicPolygonFans HyperbolicTriangles HyperbolicKleinMap
open HyperbolicIntrinsicAngles HyperbolicGeodesicHulls
open scoped UpperHalfPlane ENNReal

theorem pairwise_aeDisjoint (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (horder : OrderedRays a v n) :
    (↑(Finset.range n) : Set ℕ).Pairwise
      (fun i j => AEDisjoint (volume : Measure ℍ) (triangle a (v i) (v (i + 1)))
        (triangle a (v j) (v (j + 1)))) := by
  intro i hi j hj hij
  have hin : i < n := Finset.mem_range.mp hi
  have hjn : j < n := Finset.mem_range.mp hj
  change volume (triangle a (v i) (v (i + 1)) ∩ triangle a (v j) (v (j + 1))) = 0
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact intersection_null a v n horder hlt hjn
  · rw [inter_comm]
    exact intersection_null a v n horder hgt hin

theorem area_eq_sum (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n)
    (horder : OrderedRays a v n) (hedge : SupportingEdges a v n) :
    volume (polygon a v n) = ∑ i ∈ Finset.range n, volume (triangle a (v i) (v (i + 1))) := by
  rw [polygon_eq_fan a v n hn horder hedge]
  exact measure_biUnion_finset₀ (pairwise_aeDisjoint a v n horder)
    (fun i _ => (measurableSet_triangle a (v i) (v (i + 1))).nullMeasurableSet)

theorem real_area_eq_sum (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n)
    (horder : OrderedRays a v n) (hedge : SupportingEdges a v n) :
    (volume (polygon a v n)).toReal = ∑ i ∈ Finset.range n, (volume (triangle a (v i) (v (i + 1)))).toReal := by
  rw [area_eq_sum a v n hn horder hedge]
  exact ENNReal.toReal_sum (fun i _ => (area_triangle_lt_top a (v i) (v (i + 1))).ne)

theorem triangle_distinct (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (horder : OrderedRays a v n) {i : ℕ} (hi : i < n) :
    a ≠ v i ∧ a ≠ v (i + 1) ∧ v i ≠ v (i + 1) := by
  have hD := horder i (i + 1) (by omega) (by omega)
  obtain ⟨hab, hac, hbc⟩ := PlanarFanIntersections.positive_distinct hD
  exact ⟨fun he => hab (congrArg point he), fun he => hac (congrArg point he), fun he => hbc (congrArg point he)⟩

theorem real_area_angle_sum (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n)
    (horder : OrderedRays a v n) (hedge : SupportingEdges a v n) :
    (volume (polygon a v n)).toReal = (n : ℝ) * Real.pi -
      ∑ i ∈ Finset.range n, angleSum a (v i) (v (i + 1)) := by
  rw [real_area_eq_sum a v n hn horder hedge]
  calc
    _ = ∑ i ∈ Finset.range n, (Real.pi - angleSum a (v i) (v (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨hab, hac, hbc⟩ := triangle_distinct a v n horder (Finset.mem_range.mp hi)
      exact HyperbolicFiniteTriangleAreaAngle.real_area_formula a (v i) (v (i + 1)) hab hac hbc
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem polygon_subset {S : Set ℍ} (hS : GeodesicallyConvex S) (a : ℍ) (v : ℕ → ℍ) (n : ℕ)
    (ha : a ∈ S) (hv : ∀ i : ℕ, i ≤ n → v i ∈ S) : polygon a v n ⊆ S := by
  apply hull_min _ hS
  rintro z (rfl | ⟨i, hi, rfl⟩)
  · exact ha
  · exact hv i hi

end VeechDichotomy.HyperbolicFanAreas
