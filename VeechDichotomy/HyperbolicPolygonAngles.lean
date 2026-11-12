module

public import VeechDichotomy.StrictKleinPolygons

/-! Actual polygon corner angles are the sum of the actual fan triangle
angles. Root angles telescope by the proved positive-cone ordering;
each interior diagonal splits its actual polygon corner angle. A finite
sum identity then accounts for every actual vertex exactly once. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicPolygonAngles

open HyperbolicIntrinsicAngles HyperbolicPolygonFans StrictKleinPolygons
open scoped UpperHalfPlane

def polygonAngleSum (a : ℍ) (v : ℕ → ℍ) (n : ℕ) : ℝ :=
  angleAt a (v 0) (v n) + angleAt (v 0) a (v 1) +
    (∑ i ∈ Finset.range (n - 1), angleAt (v (i + 1)) (v i) (v (i + 2))) +
    angleAt (v n) a (v (n - 1))

theorem root_angle_sum (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n) (horder : OrderedRays a v n) :
    (∑ i ∈ Finset.range n, angleAt a (v i) (v (i + 1))) = angleAt a (v 0) (v n) := by
  revert hn horder
  induction n with
  | zero => intro hn _; omega
  | succ n ih =>
    intro _ horder
    by_cases hz : n = 0
    · subst n
      simp
    · have hn : 0 < n := Nat.pos_of_ne_zero hz
      have hprefix : OrderedRays a v n := fun i j hij hj => horder i j hij (hj.trans (Nat.le_succ n))
      rw [Finset.sum_range_succ, ih hn hprefix]
      exact (root_angle_split horder hn (Nat.lt_succ_self n) le_rfl).symm

theorem regroup_sums (A B : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, (A i + B i)) = A 0 +
      (∑ i ∈ Finset.range (n - 1), (B i + A (i + 1))) + B (n - 1) := by
  have hA : (∑ i ∈ Finset.range n, A i) = (∑ i ∈ Finset.range (n - 1), A (i + 1)) + A 0 := by
    simpa only [Nat.sub_add_cancel hn] using Finset.sum_range_succ' A (n - 1)
  have hB : (∑ i ∈ Finset.range n, B i) = (∑ i ∈ Finset.range (n - 1), B i) + B (n - 1) := by
    simpa only [Nat.sub_add_cancel hn] using Finset.sum_range_succ B (n - 1)
  rw [Finset.sum_add_distrib, hA, hB, Finset.sum_add_distrib]
  ring

theorem fan_angle_sum (a : ℍ) (v : ℕ → ℍ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    (∑ i ∈ Finset.range n, angleSum a (v i) (v (i + 1))) = polygonAngleSum a v n := by
  have hmiddle : (∑ i ∈ Finset.range (n - 1),
      (angleAt (v (i + 1)) a (v i) + angleAt (v (i + 1)) a (v ((i + 1) + 1)))) =
      ∑ i ∈ Finset.range (n - 1), angleAt (v (i + 1)) (v i) (v (i + 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (interior_angle_split h (by have hi' := Finset.mem_range.mp hi; omega)).symm
  calc
    _ = (∑ i ∈ Finset.range n, angleAt a (v i) (v (i + 1))) +
        (∑ i ∈ Finset.range n, (angleAt (v i) a (v (i + 1)) + angleAt (v (i + 1)) a (v i))) := by
      simp only [angleSum, Finset.sum_add_distrib]
      ring
    _ = angleAt a (v 0) (v n) + (angleAt (v 0) a (v 1) +
        (∑ i ∈ Finset.range (n - 1),
          (angleAt (v (i + 1)) a (v i) + angleAt (v (i + 1)) a (v ((i + 1) + 1)))) +
        angleAt (v ((n - 1) + 1)) a (v (n - 1))) := by
      rw [root_angle_sum a v n hn h.1, regroup_sums _ _ n hn]
    _ = _ := by
      rw [hmiddle]
      simp only [polygonAngleSum, Nat.sub_add_cancel hn]
      ring

end VeechDichotomy.HyperbolicPolygonAngles
