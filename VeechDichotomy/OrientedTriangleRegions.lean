module

public import VeechDichotomy.ComplexOrientedTriangles

/-! Literal three-half-plane membership and common-edge identities for
actual complex triangles. Explicit barycentric coefficients are obtained
from determinants and their actual weighted vector identity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.OrientedTriangleRegions

open Set ComplexOrientedTriangles

def region (a b c : ℂ) : Set ℂ := convexHull ℝ {a, b, c}

theorem combination_mem (a b c : ℂ) (α μ ν : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hsum : α + μ + ν = 1) : α • a + μ • b + ν • c ∈ region a b c := by
  have hconv : Convex ℝ (region a b c) := convex_convexHull ℝ _
  have ha : a ∈ region a b c := subset_convexHull ℝ _ (by simp)
  have hb : b ∈ region a b c := subset_convexHull ℝ _ (by simp)
  have hc : c ∈ region a b c := subset_convexHull ℝ _ (by simp)
  by_cases hz : μ + ν = 0
  · have hμz : μ = 0 := by linarith
    have hνz : ν = 0 := by linarith
    have hαo : α = 1 := by linarith
    simpa only [hμz, hνz, hαo, zero_smul, one_smul, add_zero] using ha
  · have hpos : 0 < μ + ν := lt_of_le_of_ne (add_nonneg hμ hν) (fun he => hz he.symm)
    let q := (μ / (μ + ν)) • b + (ν / (μ + ν)) • c
    have hq : q ∈ region a b c := hconv hb hc
      (div_nonneg hμ hpos.le) (div_nonneg hν hpos.le) (by rw [← add_div, div_self hz])
    have h := hconv ha hq hα hpos.le (by linarith only [hsum])
    have he : α • a + (μ + ν) • q = α • a + μ • b + ν • c := by
      have hμc : (μ + ν) * (μ / (μ + ν)) = μ := by field_simp [hz]
      have hνc : (μ + ν) * (ν / (μ + ν)) = ν := by field_simp [hz]
      simp only [q, smul_add, smul_smul, hμc, hνc]
      abel
    exact he ▸ h

theorem barycentric_identity (a b c z : ℂ) (hD : orient a b c ≠ 0) :
    (orient b c z / orient a b c) • a + (orient c a z / orient a b c) • b +
      (orient a b z / orient a b c) • c = z := by
  calc
    _ = (1 / orient a b c) •
        ((orient b c z) • a + (orient c a z) • b + (orient a b z) • c) := by
      simp only [smul_add, smul_smul, div_eq_mul_inv]
      module
    _ = (1 / orient a b c) • ((orient a b c) • z) := by rw [weighted_identity]
    _ = z := by rw [smul_smul, one_div, inv_mul_cancel₀ hD, one_smul]

theorem halfPlane_bound (a b u v w : ℂ) (hu : 0 ≤ orient a b u)
    (hv : 0 ≤ orient a b v) (hw : 0 ≤ orient a b w) :
    region u v w ⊆ {z : ℂ | 0 ≤ orient a b z} := by
  apply convexHull_min _ (convex_halfPlane a b)
  simp only [insert_subset_iff, singleton_subset_iff, mem_ofPred_eq]
  exact ⟨hu, hv, hw⟩

theorem mem_iff (a b c z : ℂ) (hD : 0 < orient a b c) :
    z ∈ region a b c ↔ 0 ≤ orient a b z ∧ 0 ≤ orient b c z ∧ 0 ≤ orient c a z := by
  constructor
  · intro hz
    have hBC : 0 ≤ orient b c a := by rw [← orient_rotate]; exact hD.le
    have hCA : 0 ≤ orient c a b := by rw [orient_rotate]; exact hD.le
    exact ⟨halfPlane_bound a b a b c (by simp) (by simp) hD.le hz,
      halfPlane_bound b c a b c hBC (by simp) (by simp) hz,
      halfPlane_bound c a a b c (by simp) hCA (by simp) hz⟩
  · rintro ⟨hab, hbc, hca⟩
    have hsum : orient b c z / orient a b c + orient c a z / orient a b c +
        orient a b z / orient a b c = 1 := by
      rw [← add_div, ← add_div, orientation_sum, div_self hD.ne']
    have hm := combination_mem a b c _ _ _ (div_nonneg hbc hD.le) (div_nonneg hca hD.le)
      (div_nonneg hab hD.le) hsum
    rwa [barycentric_identity a b c z hD.ne'] at hm

theorem zero_side_mem_edge (a b c z : ℂ) (hD : 0 < orient a b c)
    (hz : z ∈ region a b c) (hside : orient c a z = 0) : z ∈ segment ℝ a c := by
  have hs := (mem_iff a b c z hD).mp hz
  have hsum := orientation_sum a b c z
  have hpoint := barycentric_identity a b c z hD.ne'
  rw [hside, zero_div, zero_smul, add_zero] at hpoint
  refine ⟨orient b c z / orient a b c, orient a b z / orient a b c,
    div_nonneg hs.2.1 hD.le, div_nonneg hs.1 hD.le, ?_, hpoint⟩
  rw [← add_div]
  have he : orient b c z + orient a b z = orient a b c := by rw [hside] at hsum; linarith
  rw [he, div_self hD.ne']

end VeechDichotomy.OrientedTriangleRegions
