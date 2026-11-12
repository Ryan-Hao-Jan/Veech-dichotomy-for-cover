module

public import VeechDichotomy.OrderedPlanarFans

/-! Distinct actual triangles in an ordered planar fan meet only on
an actual root diagonal. Their opposite determinant inequalities force
the common-side equality, and the proved triangle edge theorem gives
the full literal segment containment. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PlanarFanIntersections

open Set ComplexOrientedTriangles OrientedTriangleRegions OrderedPlanarFans

theorem positive_distinct {a b c : ℂ} (hD : 0 < orient a b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    simp only [orient_same_left, lt_self_iff_false] at hD
  · rintro rfl
    simp only [orient_same_right, lt_self_iff_false] at hD
  · rintro rfl
    simp only [orient_same_last, lt_self_iff_false] at hD

theorem intersection_subset_diagonal (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (horder : OrderedRays a v n)
    {i j : ℕ} (hij : i < j) (hj : j < n) :
    region a (v i) (v (i + 1)) ∩ region a (v j) (v (j + 1)) ⊆ segment ℝ a (v (i + 1)) := by
  intro z hz
  have hD := horder i (i + 1) (by omega) (by omega)
  have hfirst := ((OrientedTriangleRegions.mem_iff a (v i) (v (i + 1)) z hD).mp hz.1).2.2
  have hmid : 0 ≤ orient a (v (i + 1)) (v j) := by
    by_cases he : i + 1 = j
    · simp [← he]
    · exact (horder (i + 1) j (by omega) hj.le).le
  have hlast : 0 ≤ orient a (v (i + 1)) (v (j + 1)) :=
    (horder (i + 1) (j + 1) (by omega) (by omega)).le
  have hsecond : 0 ≤ orient a (v (i + 1)) z :=
    halfPlane_bound a (v (i + 1)) a (v j) (v (j + 1)) (by simp) hmid hlast hz.2
  have he : orient (v (i + 1)) a z = 0 := by
    rw [orient_swap (v (i + 1)) a z] at hfirst ⊢
    linarith
  exact zero_side_mem_edge a (v i) (v (i + 1)) z hD hz.1 he

end VeechDichotomy.PlanarFanIntersections
