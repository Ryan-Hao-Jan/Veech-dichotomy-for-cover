module

public import VeechDichotomy.HyperbolicPolygonVertexSums

/-! The actual native lattice bounds the sum of the actual Dirichlet
corner deficits over EVERY finite subset of true corners. The polygon
enumeration and area budget are constructed, each polygon corner angle
is compared with the actual region's angular width, and the literal
finite vertex sum counts every selected corner exactly once. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFiniteCornerDeficitBudget

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions HyperbolicDirichletCorners
open HyperbolicPolygonFans HyperbolicPolygonAngles HyperbolicPolygonAreaAngle HyperbolicPolygonVertexSums
open StrictKleinPolygons DirichletCornerAngles HyperbolicIntrinsicAngles
open scoped UpperHalfPlane ENNReal

theorem ordered_sum_le_exterior (Γ : Subgroup SL2) (p a : ℍ) (v : ℕ → ℍ) (n : ℕ)
    (hn : 0 < n) (h : OrderedRays a v n) (ha : a ∈ region Γ p)
    (hv : ∀ i : ℕ, i ≤ n → v i ∈ region Γ p) :
    (∑ w ∈ vertexFinset a v n, deficit Γ p w) ≤ exteriorSum a v n := by
  have hroot := deficit_le_corner Γ p a (v 0) (v n) (hv 0 (Nat.zero_le _)) (hv n le_rfl)
    (root_ne_chain hn h 0 (Nat.zero_le _)).symm (root_ne_chain hn h n le_rfl).symm
  have hfirst := deficit_le_corner Γ p (v 0) a (v 1) ha (hv 1 (by omega))
    (root_ne_chain hn h 0 (Nat.zero_le _))
    (ordered_distinct h (show 0 < 1 by omega) (show 1 ≤ n by omega)).2.2.symm
  have hmiddle : (∑ i ∈ Finset.range (n - 1), deficit Γ p (v (i + 1))) ≤
      ∑ i ∈ Finset.range (n - 1), (Real.pi - angleAt (v (i + 1)) (v i) (v (i + 2))) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i + 2 ≤ n := by have hlt := Finset.mem_range.mp hi; omega
    exact deficit_le_corner Γ p (v (i + 1)) (v i) (v (i + 2)) (hv i (by omega)) (hv (i + 2) hi')
      (ordered_distinct h (show i < i + 1 by omega) (show i + 1 ≤ n by omega)).2.2
      (ordered_distinct h (show i + 1 < i + 2 by omega) hi').2.2.symm
  have hlast := deficit_le_corner Γ p (v n) a (v (n - 1)) ha (hv (n - 1) (by omega))
    (root_ne_chain hn h n le_rfl)
    (ordered_distinct h (show n - 1 < n by omega) le_rfl).2.2
  rw [sum_vertices (deficit Γ p) a v n hn h]
  unfold exteriorSum
  linarith only [hroot, hfirst, hmiddle, hlast]

theorem sum_deficit_bound (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (S : Finset ℍ)
    (hS : ∀ z ∈ S, z ∈ corners Γ p) :
    (∑ w ∈ S, deficit Γ p w) ≤ (volume (region Γ p)).toReal + 2 * Real.pi := by
  classical
  by_cases hcard : 3 ≤ S.card
  · obtain ⟨a, v, n, ha, hn, _, hvertices, hstrict⟩ := NativeFiniteCornerPolygons.enumerate Γ p S hS hcard
    have hvD : ∀ i : ℕ, i ≤ n → v i ∈ region Γ p := by
      intro i hi
      have hm : v i ∈ vertices a v n := Or.inr ⟨i, hi, rfl⟩
      rw [hvertices] at hm
      exact (hS (v i) hm).1
    have hcompare := ordered_sum_le_exterior Γ p a v n hn hstrict.1 (hS a ha).1 hvD
    rw [vertexFinset_eq hvertices] at hcompare
    exact hcompare.trans (NativeDirichletPolygonDeficit.exterior_bound Γ hΓ p a v n hn hstrict (hS a ha).1 hvD)
  · have hsum : (∑ w ∈ S, deficit Γ p w) ≤ (S.card : ℝ) * Real.pi := by
      calc
        _ ≤ ∑ _ ∈ S, Real.pi := Finset.sum_le_sum (fun w _ => deficit_le_pi Γ p w)
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    have hcount : (S.card : ℝ) ≤ 2 := by exact_mod_cast (show S.card ≤ 2 by omega)
    have hprod := mul_le_mul_of_nonneg_right hcount Real.pi_pos.le
    have harea : 0 ≤ (volume (region Γ p)).toReal := ENNReal.toReal_nonneg
    linarith only [hsum, hprod, harea]

end VeechDichotomy.NativeFiniteCornerDeficitBudget
