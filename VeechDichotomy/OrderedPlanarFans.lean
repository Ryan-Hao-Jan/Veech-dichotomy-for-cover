module

public import VeechDichotomy.OrientedTriangleRegions
public import Mathlib.Data.Nat.Find

/-! A literal fan triangulates the convex hull of an ordered complex
vertex chain. The hypotheses are actual determinant order and actual
supporting-edge inequalities. All triangle membership and the entire
union identity are proved, rather than supplied as triangulation data. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.OrderedPlanarFans

open Set ComplexOrientedTriangles OrientedTriangleRegions

def vertices (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : Set ℂ := insert a (v '' Iic n)
def polygon (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : Set ℂ := convexHull ℝ (vertices a v n)

def OrderedRays (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : Prop :=
  ∀ i j : ℕ, i < j → j ≤ n → 0 < orient a (v i) (v j)

def SupportingEdges (_a : ℂ) (v : ℕ → ℂ) (n : ℕ) : Prop :=
  ∀ i : ℕ, i < n → ∀ j : ℕ, j ≤ n → 0 ≤ orient (v i) (v (i + 1)) (v j)

theorem discrete_crossing (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hzero : 0 ≤ f 0) (hlast : f n ≤ 0) :
    ∃ i : ℕ, i < n ∧ 0 ≤ f i ∧ f (i + 1) ≤ 0 := by
  have hex : ∃ i : ℕ, i < n ∧ f (i + 1) ≤ 0 :=
    ⟨n - 1, by omega, by simpa only [Nat.sub_add_cancel hn] using hlast⟩
  let i := Nat.find hex
  have hi : i < n ∧ f (i + 1) ≤ 0 := Nat.find_spec hex
  refine ⟨i, hi.1, ?_, hi.2⟩
  by_cases hz : i = 0
  · simpa only [hz] using hzero
  · have hipos : 0 < i := Nat.pos_of_ne_zero hz
    have hprev : ¬(i - 1 < n ∧ f ((i - 1) + 1) ≤ 0) := Nat.find_min hex (show i - 1 < i by omega)
    have hnot : ¬f i ≤ 0 := by
      intro hfi
      apply hprev
      exact ⟨by omega, by simpa only [Nat.sub_add_cancel hipos] using hfi⟩
    exact (lt_of_not_ge hnot).le

theorem halfPlane_polygon (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (u w : ℂ)
    (ha : 0 ≤ orient u w a) (hv : ∀ i : ℕ, i ≤ n → 0 ≤ orient u w (v i)) :
    polygon a v n ⊆ {z : ℂ | 0 ≤ orient u w z} := by
  apply convexHull_min _ (convex_halfPlane u w)
  rintro z (rfl | ⟨i, hi, rfl⟩)
  · exact ha
  · exact hv i hi

theorem triangle_subset_polygon (a : ℂ) (v : ℕ → ℂ) (n i : ℕ) (hi : i < n) :
    region a (v i) (v (i + 1)) ⊆ polygon a v n := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  simp only [insert_subset_iff, singleton_subset_iff]
  refine ⟨subset_convexHull ℝ _ (mem_insert _ _), ?_, ?_⟩
  · exact subset_convexHull ℝ _ (Or.inr ⟨i, hi.le, rfl⟩)
  · exact subset_convexHull ℝ _ (Or.inr ⟨i + 1, by change i + 1 ≤ n; omega, rfl⟩)

theorem mem_fan_of_mem_polygon (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (horder : OrderedRays a v n) (hedge : SupportingEdges a v n) {z : ℂ} (hz : z ∈ polygon a v n) :
    ∃ i : ℕ, i < n ∧ z ∈ region a (v i) (v (i + 1)) := by
  have hzero : 0 ≤ orient a (v 0) z := by
    apply halfPlane_polygon a v n a (v 0) (by simp) _ hz
    intro j hj
    by_cases he : j = 0
    · simp [he]
    · exact (horder 0 j (Nat.pos_of_ne_zero he) hj).le
  have hlast : orient a (v n) z ≤ 0 := by
    have h := halfPlane_polygon a v n (v n) a (by simp) (fun j hj => ?_) hz
    · change 0 ≤ orient (v n) a z at h
      rw [orient_swap (v n) a z] at h
      linarith
    · by_cases he : j = n
      · simp [he]
      · rw [orient_rotate]
        exact (horder j n (lt_of_le_of_ne hj he) le_rfl).le
  obtain ⟨i, hi, hleft, hright⟩ := discrete_crossing (fun j => orient a (v j) z) n hn hzero hlast
  refine ⟨i, hi, (OrientedTriangleRegions.mem_iff a (v i) (v (i + 1)) z
    (horder i (i + 1) (by omega) (by omega))).mpr ⟨hleft, ?_, ?_⟩⟩
  · exact halfPlane_polygon a v n (v i) (v (i + 1))
      (by rw [← orient_rotate]; exact horder i (i + 1) (by omega) (by omega) |>.le)
      (hedge i hi) hz
  · rw [orient_swap (v (i + 1)) a z]
    exact neg_nonneg.mpr hright

theorem polygon_eq_fan (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n)
    (horder : OrderedRays a v n) (hedge : SupportingEdges a v n) :
    polygon a v n = ⋃ i ∈ Finset.range n, region a (v i) (v (i + 1)) := by
  apply Subset.antisymm
  · intro z hz
    simp only [mem_iUnion, exists_prop, Finset.mem_range]
    exact mem_fan_of_mem_polygon a v n hn horder hedge hz
  · intro z hz
    simp only [mem_iUnion, exists_prop, Finset.mem_range] at hz
    obtain ⟨i, hi, hz⟩ := hz
    exact triangle_subset_polygon a v n i hi hz

end VeechDichotomy.OrderedPlanarFans
