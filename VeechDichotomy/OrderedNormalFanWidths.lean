module

public import VeechDichotomy.PlanarPolygonVertexSums

/-! The actual normal widths of a strictly convex ordered complex
polygon sum to 2*pi. Each actual cone is identified with its adjacent
dual rays; literal vertex sums and the proved Euclidean corner sum
give the total. No angular-partition or turning-angle axiom is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.OrderedNormalFanWidths

open Set ComplexOrientedTriangles OrderedPlanarFans OrderedPolygonNormalCones PlanarPolygonAngles
open HyperbolicRegionAngles PlanarPolygonVertexSums

theorem width_root (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    vectorWidth (FiniteSiteNormalFans.sector (vertices a v n) a) = Real.pi - angleAt a (v 0) (v n) := by
  have hw := width_corner (vertices a v n) (v n) a (v 0) (chain_mem a v n n le_rfl)
    (chain_mem a v n 0 (Nat.zero_le _)) (h.1 0 n hn le_rfl) (support_last h.1) (support_first h.1)
  rw [angleAt_comm a (v n) (v 0)] at hw
  exact hw

theorem width_first (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    vectorWidth (FiniteSiteNormalFans.sector (vertices a v n) (v 0)) = Real.pi - angleAt (v 0) a (v 1) := by
  have hD : 0 < orient (v 0) (v 1) a := by rw [← orient_rotate]; exact h.1 0 1 (by omega) (by omega)
  exact width_corner (vertices a v n) a (v 0) (v 1) (root_mem a v n) (chain_mem a v n 1 (by omega)) hD
    (support_first h.1) (support_edge h hn)

theorem width_middle (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (h : StrictlyOrdered a v n) {i : ℕ} (hi : i + 2 ≤ n) :
    vectorWidth (FiniteSiteNormalFans.sector (vertices a v n) (v (i + 1))) =
      Real.pi - angleAt (v (i + 1)) (v i) (v (i + 2)) := by
  have hD : 0 < orient (v (i + 1)) (v (i + 2)) (v i) := by
    rw [← orient_rotate]
    exact h.2 i (i + 1) (i + 2) (by omega) (by omega) hi
  exact width_corner (vertices a v n) (v i) (v (i + 1)) (v (i + 2))
    (chain_mem a v n i (by omega)) (chain_mem a v n (i + 2) hi) hD
    (support_edge h (show i < n by omega)) (support_edge h (show i + 1 < n by omega))

theorem width_last (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    vectorWidth (FiniteSiteNormalFans.sector (vertices a v n) (v n)) = Real.pi - angleAt (v n) a (v (n - 1)) := by
  have hD : 0 < orient (v n) a (v (n - 1)) := by
    rw [orient_rotate]
    exact h.1 (n - 1) n (by omega) le_rfl
  have hp : ∀ t ∈ vertices a v n, 0 ≤ orient (v (n - 1)) (v n) t := by
    simpa only [Nat.sub_add_cancel hn] using support_edge h (show n - 1 < n by omega)
  have hw := width_corner (vertices a v n) (v (n - 1)) (v n) a
    (chain_mem a v n (n - 1) (by omega)) (root_mem a v n) hD hp (support_last h.1)
  rw [angleAt_comm (v n) (v (n - 1)) a] at hw
  exact hw

theorem sum_widths (a : ℂ) (v : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (h : StrictlyOrdered a v n) :
    (∑ s ∈ vertexFinset a v n, vectorWidth (FiniteSiteNormalFans.sector (vertices a v n) s)) = 2 * Real.pi := by
  have hm : (∑ i ∈ Finset.range (n - 1), vectorWidth (FiniteSiteNormalFans.sector (vertices a v n) (v (i + 1)))) =
      ∑ i ∈ Finset.range (n - 1), (Real.pi - angleAt (v (i + 1)) (v i) (v (i + 2))) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact width_middle a v n h (by have hi' := Finset.mem_range.mp hi; omega)
  rw [sum_vertices _ a v n hn h.1, width_root a v n hn h, width_first a v n hn h, width_last a v n hn h, hm]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_sub (show 1 ≤ n from hn), Nat.cast_one]
  have hs := polygon_angle_sum a v n hn h
  unfold polygonAngleSum at hs
  linarith only [hs]

end VeechDichotomy.OrderedNormalFanWidths
