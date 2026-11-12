module

public import VeechDichotomy.CircleExposedPoints
public import Mathlib.Geometry.Euclidean.Triangle

/-! Actual Euclidean angle sums for strictly ordered complex polygons.
Concrete positive determinants give the two diagonal angle additions;
the actual Euclidean triangle angle sum and finite regrouping then prove
the polygon sum and total exterior angle, without a polygon-angle axiom. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PlanarPolygonAngles

open Set ComplexOrientedTriangles
open scoped NNReal

def angleAt (a b c : ℂ) : ℝ := InnerProductGeometry.angle (b - a) (c - a)
def angleSum (a b c : ℂ) : ℝ := angleAt a b c + angleAt b a c + angleAt c a b
def PositiveTriples (v : ℕ → ℂ) (n : ℕ) : Prop :=
  ∀ i j k : ℕ, i < j → j < k → k ≤ n → 0 < orient (v i) (v j) (v k)
def StrictlyOrdered (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : Prop :=
  OrderedPlanarFans.OrderedRays a v n ∧ PositiveTriples v n

theorem angleAt_comm (a b c : ℂ) : angleAt a b c = angleAt a c b := InnerProductGeometry.angle_comm _ _

theorem triangle_angle_sum (a b c : ℂ) (hab : a ≠ b) : angleSum a b c = Real.pi := by
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := b) (p₂ := a) c hab
  change angleAt a b c + angleAt c a b + angleAt b c a = Real.pi at h
  rw [angleAt_comm b c a] at h
  unfold angleSum
  linarith

theorem supportingEdges {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (h : StrictlyOrdered a v n) :
    OrderedPlanarFans.SupportingEdges a v n := by
  intro i hi j hj
  by_cases he : j = i
  · simp [he]
  by_cases he' : j = i + 1
  · simp [he']
  rcases lt_or_gt_of_ne he with hji | hij
  · rw [← orient_rotate (v j) (v i) (v (i + 1))]
    exact (h.2 j i (i + 1) hji (by omega) (by omega)).le
  · exact (h.2 i (i + 1) j (by omega) (by omega) hj).le

theorem angle_addition (a b c p : ℂ) (hspan : p - a ∈ Submodule.span ℝ≥0 {b - a, c - a}) (hpa : p ≠ a) :
    angleAt a b c = angleAt a b p + angleAt a p c :=
  InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span (sub_ne_zero.mpr hpa) hspan

theorem root_angle_split {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (h : OrderedPlanarFans.OrderedRays a v n)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k ≤ n) :
    angleAt a (v i) (v k) = angleAt a (v i) (v j) + angleAt a (v j) (v k) := by
  have hspan : v j - a ∈ Submodule.span ℝ≥0 {v i - a, v k - a} :=
    ComplexPositiveCones.mem_span _ _ _ (h i k (hij.trans hjk) hk)
      (h i j hij (hjk.le.trans hk)).le (h j k hjk hk).le
  exact angle_addition a (v i) (v k) (v j) hspan
    (PlanarFanIntersections.positive_distinct (h i j hij (hjk.le.trans hk))).2.1.symm

theorem interior_angle_split {a : ℂ} {v : ℕ → ℂ} {n i : ℕ} (h : StrictlyOrdered a v n) (hi : i + 2 ≤ n) :
    angleAt (v (i + 1)) (v i) (v (i + 2)) =
      angleAt (v (i + 1)) a (v i) + angleAt (v (i + 1)) a (v (i + 2)) := by
  have hD : 0 < orient (v (i + 1)) (v (i + 2)) (v i) := by
    rw [← orient_rotate]
    exact h.2 i (i + 1) (i + 2) (by omega) (by omega) hi
  have hl : 0 ≤ orient (v (i + 1)) (v (i + 2)) a := by
    rw [← orient_rotate]
    exact (h.1 (i + 1) (i + 2) (by omega) hi).le
  have hr : 0 ≤ orient (v (i + 1)) a (v i) := by
    rw [orient_rotate]
    exact (h.1 i (i + 1) (by omega) (by omega)).le
  have hspan : a - v (i + 1) ∈ Submodule.span ℝ≥0 {v (i + 2) - v (i + 1), v i - v (i + 1)} :=
    ComplexPositiveCones.mem_span _ _ _ hD hl hr
  have hne : a ≠ v (i + 1) :=
    (PlanarFanIntersections.positive_distinct (h.1 i (i + 1) (by omega) (by omega))).2.1
  have hang := angle_addition (v (i + 1)) (v (i + 2)) (v i) a hspan hne
  rw [angleAt_comm (v (i + 1)) (v (i + 2)) (v i), angleAt_comm (v (i + 1)) (v (i + 2)) a] at hang
  linarith

def polygonAngleSum (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : ℝ :=
  angleAt a (v 0) (v n) + angleAt (v 0) a (v 1) +
    (∑ i ∈ Finset.range (n - 1), angleAt (v (i + 1)) (v i) (v (i + 2))) + angleAt (v n) a (v (n - 1))

theorem root_angle_sum (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (horder : OrderedPlanarFans.OrderedRays a v n) :
    (∑ i ∈ Finset.range n, angleAt a (v i) (v (i + 1))) = angleAt a (v 0) (v n) := by
  revert hn horder
  induction n with
  | zero => intro hn _; omega
  | succ n ih =>
    intro _ horder
    by_cases hz : n = 0
    · subst n; simp
    · have hn : 0 < n := Nat.pos_of_ne_zero hz
      have hp : OrderedPlanarFans.OrderedRays a v n := fun i j hij hj => horder i j hij (hj.trans (Nat.le_succ n))
      rw [Finset.sum_range_succ, ih hn hp]
      exact (root_angle_split horder hn (Nat.lt_succ_self n) le_rfl).symm

theorem fan_angle_sum (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    (∑ i ∈ Finset.range n, angleSum a (v i) (v (i + 1))) = polygonAngleSum a v n := by
  have hm : (∑ i ∈ Finset.range (n - 1),
      (angleAt (v (i + 1)) a (v i) + angleAt (v (i + 1)) a (v ((i + 1) + 1)))) =
      ∑ i ∈ Finset.range (n - 1), angleAt (v (i + 1)) (v i) (v (i + 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (interior_angle_split h (by have hi' := Finset.mem_range.mp hi; omega)).symm
  calc
    _ = (∑ i ∈ Finset.range n, angleAt a (v i) (v (i + 1))) +
        (∑ i ∈ Finset.range n, (angleAt (v i) a (v (i + 1)) + angleAt (v (i + 1)) a (v i))) := by
      simp only [angleSum, Finset.sum_add_distrib]; ring
    _ = angleAt a (v 0) (v n) + (angleAt (v 0) a (v 1) +
        (∑ i ∈ Finset.range (n - 1),
          (angleAt (v (i + 1)) a (v i) + angleAt (v (i + 1)) a (v ((i + 1) + 1)))) +
        angleAt (v ((n - 1) + 1)) a (v (n - 1))) := by
      rw [root_angle_sum a v n hn h.1, HyperbolicPolygonAngles.regroup_sums _ _ n hn]
    _ = _ := by rw [hm]; simp only [polygonAngleSum, Nat.sub_add_cancel hn]; ring

theorem polygon_angle_sum (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    polygonAngleSum a v n = (n : ℝ) * Real.pi := by
  rw [← fan_angle_sum a v n hn h]
  calc
    _ = ∑ _i ∈ Finset.range n, Real.pi := by
      apply Finset.sum_congr rfl
      intro i hi
      have hD := h.1 i (i + 1) (by omega) (by have hi' := Finset.mem_range.mp hi; omega)
      exact triangle_angle_sum a (v i) (v (i + 1)) (PlanarFanIntersections.positive_distinct hD).1
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end VeechDichotomy.PlanarPolygonAngles
