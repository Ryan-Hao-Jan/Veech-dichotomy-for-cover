module

public import VeechDichotomy.ComplexPositiveCones

/-! Concrete strict convex ordering conditions on actual Klein vertices.
Positive determinants for ordered triples imply supporting-edge signs
and the actual tangent-cone conditions for root and interior corner
angle addition. No polygon area or triangulation identity is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.StrictKleinPolygons

open ComplexOrientedTriangles HyperbolicKleinMap HyperbolicPolygonFans HyperbolicIntrinsicAngles
open scoped UpperHalfPlane NNReal

def PositiveTriples (v : ℕ → ℍ) (n : ℕ) : Prop :=
  ∀ i j k : ℕ, i < j → j < k → k ≤ n → 0 < orient (point (v i)) (point (v j)) (point (v k))

def StrictlyOrdered (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : Prop :=
  OrderedRays a v n ∧ PositiveTriples v n

theorem supportingEdges {a : ℍ} {v : ℕ → ℍ} {n : ℕ} (h : StrictlyOrdered a v n) : SupportingEdges a v n := by
  intro i hi j hj
  by_cases he : j = i
  · simp [he]
  by_cases he' : j = i + 1
  · simp [he']
  rcases lt_or_gt_of_ne he with hji | hij
  · rw [← orient_rotate (point (v j)) (point (v i)) (point (v (i + 1)))]
    exact (h.2 j i (i + 1) hji (by omega) (by omega)).le
  · exact (h.2 i (i + 1) j (by omega) (by omega) hj).le

theorem mono {a : ℍ} {v : ℕ → ℍ} {n m : ℕ} (h : StrictlyOrdered a v n) (hmn : m ≤ n) :
    StrictlyOrdered a v m :=
  ⟨fun i j hij hj => h.1 i j hij (hj.trans hmn), fun i j k hij hjk hk => h.2 i j k hij hjk (hk.trans hmn)⟩

theorem ordered_distinct {a : ℍ} {v : ℕ → ℍ} {n : ℕ} (h : OrderedRays a v n)
    {i j : ℕ} (hij : i < j) (hj : j ≤ n) : a ≠ v i ∧ a ≠ v j ∧ v i ≠ v j := by
  obtain ⟨ha, hb, hc⟩ := PlanarFanIntersections.positive_distinct (h i j hij hj)
  exact ⟨fun he => ha (congrArg point he), fun he => hb (congrArg point he), fun he => hc (congrArg point he)⟩

theorem root_angle_split {a : ℍ} {v : ℕ → ℍ} {n : ℕ} (h : OrderedRays a v n)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k ≤ n) :
    angleAt a (v i) (v k) = angleAt a (v i) (v j) + angleAt a (v j) (v k) := by
  have hspan : point (v j) - point a ∈
      Submodule.span ℝ≥0 {point (v i) - point a, point (v k) - point a} :=
    ComplexPositiveCones.mem_span _ _ _ (h i k (hij.trans hjk) hk)
      (h i j hij (hjk.le.trans hk)).le (h j k hjk hk).le
  exact HyperbolicTriangleAngleAddition.angle_addition_of_klein hspan
    (ordered_distinct h hij (hjk.le.trans hk)).2.1.symm

theorem interior_angle_split {a : ℍ} {v : ℕ → ℍ} {n i : ℕ} (h : StrictlyOrdered a v n) (hi : i + 2 ≤ n) :
    angleAt (v (i + 1)) (v i) (v (i + 2)) =
      angleAt (v (i + 1)) a (v i) + angleAt (v (i + 1)) a (v (i + 2)) := by
  have hD : 0 < orient (point (v (i + 1))) (point (v (i + 2))) (point (v i)) := by
    rw [← orient_rotate]
    exact h.2 i (i + 1) (i + 2) (by omega) (by omega) hi
  have hleft : 0 ≤ orient (point (v (i + 1))) (point (v (i + 2))) (point a) := by
    rw [← orient_rotate]
    exact (h.1 (i + 1) (i + 2) (by omega) hi).le
  have hright : 0 ≤ orient (point (v (i + 1))) (point a) (point (v i)) := by
    rw [orient_rotate]
    exact (h.1 i (i + 1) (by omega) (by omega)).le
  have hspan : point a - point (v (i + 1)) ∈ Submodule.span ℝ≥0
      {point (v (i + 2)) - point (v (i + 1)), point (v i) - point (v (i + 1))} :=
    ComplexPositiveCones.mem_span _ _ _ hD hleft hright
  have hne : a ≠ v (i + 1) := (ordered_distinct h.1 (show i < i + 1 by omega) (by omega)).2.1
  have hang := HyperbolicTriangleAngleAddition.angle_addition_of_klein hspan hne
  rw [angleAt_comm (v (i + 1)) (v (i + 2)) (v i), angleAt_comm (v (i + 1)) (v (i + 2)) a] at hang
  linarith

end VeechDichotomy.StrictKleinPolygons
