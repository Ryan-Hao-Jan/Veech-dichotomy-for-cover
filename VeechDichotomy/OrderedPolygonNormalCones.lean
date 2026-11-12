module

public import VeechDichotomy.DualConeAngleWidth

/-! Actual normal cones of a strictly convex ordered polygon are
the duals of its two adjacent edge rays. Concrete supporting-edge
signs generate every vertex displacement by those rays; the exact
dual width theorem therefore identifies the actual exterior angles. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.OrderedPolygonNormalCones

open Set ComplexOrientedTriangles PlanarPolygonAngles OrderedPlanarFans HyperbolicRegionAngles
open scoped NNReal

theorem sector_eq_dual (V : Set ℂ) (prev w next : ℂ) (hp : prev ∈ V) (hn : next ∈ V)
    (hD : 0 < orient w next prev) (hprev : ∀ t ∈ V, 0 ≤ orient prev w t)
    (hnext : ∀ t ∈ V, 0 ≤ orient w next t) :
    FiniteSiteNormalFans.sector V w = DualConeAngleWidth.dual (prev - w) (next - w) := by
  ext u
  simp only [FiniteSiteNormalFans.sector, DualConeAngleWidth.dual, mem_ofPred_eq,
    FiniteSiteNormalFans.functional_apply]
  constructor
  · intro hu
    exact ⟨hu prev hp, hu next hn⟩
  · intro hu t ht
    have hright : 0 ≤ cross (t - w) (prev - w) := by
      change 0 ≤ orient w t prev
      rw [← orient_rotate prev w t]
      exact hprev t ht
    have hspan : t - w ∈ Submodule.span ℝ≥0 {next - w, prev - w} :=
      ComplexPositiveCones.mem_span _ _ _ hD (hnext t ht) hright
    obtain ⟨α, β, he⟩ := Submodule.mem_span_pair.mp hspan
    have he' : t - w = (α : ℝ) • (next - w) + (β : ℝ) • (prev - w) := by
      simpa only [NNReal.smul_def] using! he.symm
    rw [he', inner_add_left, real_inner_smul_left, real_inner_smul_left]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos α.property hu.2)
      (mul_nonpos_of_nonneg_of_nonpos β.property hu.1)

theorem width_corner (V : Set ℂ) (prev w next : ℂ) (hp : prev ∈ V) (hn : next ∈ V)
    (hD : 0 < orient w next prev) (hprev : ∀ t ∈ V, 0 ≤ orient prev w t)
    (hnext : ∀ t ∈ V, 0 ≤ orient w next t) :
    vectorWidth (FiniteSiteNormalFans.sector V w) = Real.pi - PlanarPolygonAngles.angleAt w prev next := by
  rw [sector_eq_dual V prev w next hp hn hD hprev hnext]
  exact DualConeAngleWidth.width_dual hD

theorem root_mem (a : ℂ) (v : ℕ → ℂ) (n : ℕ) : a ∈ vertices a v n := mem_insert _ _
theorem chain_mem (a : ℂ) (v : ℕ → ℂ) (n i : ℕ) (hi : i ≤ n) : v i ∈ vertices a v n :=
  Or.inr ⟨i, hi, rfl⟩

theorem support_first {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (h : OrderedRays a v n) :
    ∀ t ∈ vertices a v n, 0 ≤ orient a (v 0) t := by
  rintro t (rfl | ⟨j, hj, rfl⟩)
  · simp
  · by_cases he : j = 0
    · simp [he]
    · exact (h 0 j (Nat.pos_of_ne_zero he) hj).le

theorem support_last {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (h : OrderedRays a v n) :
    ∀ t ∈ vertices a v n, 0 ≤ orient (v n) a t := by
  rintro t (rfl | ⟨j, hj, rfl⟩)
  · simp
  · by_cases he : j = n
    · simp [he]
    · rw [orient_rotate]
      exact (h j n (lt_of_le_of_ne hj he) le_rfl).le

theorem support_edge {a : ℂ} {v : ℕ → ℂ} {n : ℕ} (h : StrictlyOrdered a v n) {i : ℕ} (hi : i < n) :
    ∀ t ∈ vertices a v n, 0 ≤ orient (v i) (v (i + 1)) t := by
  rintro t (rfl | ⟨j, hj, rfl⟩)
  · rw [← orient_rotate]
    exact (h.1 i (i + 1) (by omega) (by omega)).le
  · exact PlanarPolygonAngles.supportingEdges h i hi j hj

end VeechDichotomy.OrderedPolygonNormalCones
