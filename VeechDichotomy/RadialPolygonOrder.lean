module

public import VeechDichotomy.IdealRadialLimits
public import VeechDichotomy.CirclePolygonOrder

/-! Strict cyclic orders of finite circle sets with a total circle-valued
chain, and preservation of the actual determinant order by radial
approximation inside the actual Klein disk. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RadialPolygonOrder

open Set ComplexOrientedTriangles DirichletIdealRadialPoints IdealRadialLimits
open scoped UpperHalfPlane

theorem enumerate_total (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ = 1) (hcard : 3 ≤ S.card) :
    ∃ (a : ℂ) (v : ℕ → ℂ) (n : ℕ), a ∈ S ∧ (∀ i, v i ∈ S) ∧ 0 < n ∧
      n + 2 = S.card ∧ PlanarPolygonAngles.StrictlyOrdered a v n := by
  classical
  obtain ⟨a, v, n, ha, hn, hcount, hvertices, horder⟩ :=
    CirclePolygonOrder.enumerate S 1 zero_lt_one hS hcard
  let w : ℕ → ℂ := fun i => if i ≤ n then v i else a
  have hwi (i : ℕ) (hi : i ≤ n) : w i = v i := ite_eq_left hi
  have hv (i : ℕ) (hi : i ≤ n) : v i ∈ S := by
    change v i ∈ (S : Set ℂ)
    rw [← hvertices]
    exact mem_insert_of_mem _ (mem_image_of_mem v hi)
  refine ⟨a, w, n, ha, ?_, hn, hcount, ?_, ?_⟩
  · intro i
    by_cases hi : i ≤ n
    · rw [hwi i hi]
      exact hv i hi
    · simpa only [w, ite_eq_right hi] using ha
  · intro i j hij hj
    rw [hwi i (hij.le.trans hj), hwi j hj]
    exact horder.1 i j hij hj
  · intro i j k hij hjk hk
    rw [hwi i (hij.le.trans (hjk.le.trans hk)), hwi j (hjk.le.trans hk), hwi k hk]
    exact horder.2 i j k hij hjk hk

theorem orient_radial (p : ℍ) (a b c : ℂ) (t : ℝ) :
    orient (radial p a t) (radial p b t) (radial p c t) = t ^ 2 * orient a b c := by
  simp only [orient, cross, radial, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem approx_strict (p : ℍ) (a : ℂ) (v : ℕ → ℂ) (n : ℕ)
    (ha : ‖a‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (h : PlanarPolygonAngles.StrictlyOrdered a v n) (k : ℕ) :
    StrictKleinPolygons.StrictlyOrdered (approx p a ha k) (fun i => approx p (v i) (hv i) k) n := by
  have ht : 0 < time k ^ 2 := sq_pos_of_pos (time_pos k)
  constructor
  · intro i j hij hj
    change 0 < orient (HyperbolicKleinMap.point (approx p a ha k))
      (HyperbolicKleinMap.point (approx p (v i) (hv i) k))
      (HyperbolicKleinMap.point (approx p (v j) (hv j) k))
    rw [point_approx, point_approx, point_approx, orient_radial]
    exact mul_pos ht (h.1 i j hij hj)
  · intro i j l hij hjl hl
    change 0 < orient (HyperbolicKleinMap.point (approx p (v i) (hv i) k))
      (HyperbolicKleinMap.point (approx p (v j) (hv j) k))
      (HyperbolicKleinMap.point (approx p (v l) (hv l) k))
    rw [point_approx, point_approx, point_approx, orient_radial]
    exact mul_pos ht (h.2 i j l hij hjl hl)

theorem root_ne {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (hn : 0 < n)
    (h : PlanarPolygonAngles.StrictlyOrdered a v n) (i : ℕ) (hi : i ≤ n) : a ≠ v i := by
  by_cases he : i = 0
  · subst i
    exact (PlanarFanIntersections.positive_distinct (h.1 0 n hn le_rfl)).1
  · exact (PlanarFanIntersections.positive_distinct (h.1 0 i (Nat.pos_of_ne_zero he) hi)).2.1

theorem chain_ne {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (h : PlanarPolygonAngles.StrictlyOrdered a v n)
    {i j : ℕ} (hij : i ≠ j) (hi : i ≤ n) (hj : j ≤ n) : v i ≠ v j := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (PlanarFanIntersections.positive_distinct (h.1 i j hij hj)).2.2
  · exact (PlanarFanIntersections.positive_distinct (h.1 j i hji hi)).2.2.symm

end VeechDichotomy.RadialPolygonOrder
