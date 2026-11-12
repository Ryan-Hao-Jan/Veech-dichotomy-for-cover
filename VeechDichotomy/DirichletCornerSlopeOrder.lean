module

public import VeechDichotomy.ExposedRootCoordinates

/-! Actual Dirichlet corners have distinct slope keys at an exposed
corner root. Equal keys would put one actual corner on the segment from
the root to another corner, contradicting its actual exposing functional.
Strict key order gives the genuine positive Klein determinant order. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletCornerSlopeOrder

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletCorners HyperbolicKleinMap
open ComplexOrientedTriangles ExposedRootCoordinates
open scoped UpperHalfPlane

theorem mem_segment_of_ray (a u v : ℂ) (k : ℝ) (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (he : v - a = k • (u - a)) : v ∈ segment ℝ a u := by
  refine ⟨1 - k, k, sub_nonneg.mpr hk₁, hk₀, by ring, ?_⟩
  calc
    _ = a + k • (u - a) := by module
    _ = v := by rw [← he]; abel

theorem corner_not_on_other_segment (Γ : Subgroup SL2) (p w a b : ℍ) (hw : w ∈ corners Γ p)
    (ha : a ∈ region Γ p) (hb : b ∈ region Γ p) (haw : a ≠ w) (hbw : b ≠ w)
    (hseg : point w ∈ segment ℝ (point a) (point b)) : False := by
  have hmem (z : ℍ) (hz : z ∈ region Γ p) (hne : z ≠ w) : point z ∈ point '' (region Γ p \ {w}) :=
    ⟨z, ⟨hz, by simpa only [mem_singleton_iff] using hne⟩, rfl⟩
  have hsub : ({point a, point b} : Set ℂ) ⊆ point '' (region Γ p \ {w}) := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hmem a ha haw, hmem b hb hbw⟩
  apply DirichletCornerExposure.not_mem_hull_rest Γ p w hw
  apply convexHull_mono hsub
  rwa [convexHull_pair]

def key (L : ℂ →L[ℝ] ℝ) (a z : ℍ) : ℝ := ExposedRootCoordinates.slope L (point a) (point z)

theorem key_injective (Γ : Subgroup SL2) (p a : ℍ) (ha : a ∈ corners Γ p) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z ∈ region Γ p, z ≠ a → L (point z) < L (point a)) :
    InjOn (key L a) (corners Γ p \ {a}) := by
  intro u hu v hv he
  have hua : u ≠ a := by simpa only [mem_singleton_iff] using hu.2
  have hva : v ≠ a := by simpa only [mem_singleton_iff] using hv.2
  have hLu := hL u hu.1.1 hua
  have hLv := hL v hv.1.1 hva
  have hLne : L ≠ 0 := by intro hz; rw [hz] at hLu; simp at hLu
  by_contra huv
  obtain ⟨k, hk, hray⟩ := equal_slope_rays L hLne (point a) (point u) (point v) hLu hLv he
  by_cases hk₁ : k ≤ 1
  · exact corner_not_on_other_segment Γ p v a u hv.1 ha.1 hu.1.1 hva.symm huv
      (mem_segment_of_ray (point a) (point u) (point v) k hk.le hk₁ hray)
  · have hkinv : 1 / k ≤ 1 := (div_le_iff₀ hk).mpr (by linarith only [hk₁])
    have hback : point u - point a = (1 / k) • (point v - point a) := by
      rw [hray, smul_smul, one_div, inv_mul_cancel₀ hk.ne', one_smul]
    exact corner_not_on_other_segment Γ p u a v hu.1 ha.1 hv.1.1 hua.symm (fun he => huv he.symm)
      (mem_segment_of_ray (point a) (point v) (point u) (1 / k) (div_nonneg zero_le_one hk.le) hkinv hback)

theorem key_lt_orient (Γ : Subgroup SL2) (p a : ℍ) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z ∈ region Γ p, z ≠ a → L (point z) < L (point a)) (u v : ℍ)
    (hu : u ∈ region Γ p) (hv : v ∈ region Γ p) (hua : u ≠ a) (hva : v ≠ a)
    (he : key L a u < key L a v) : 0 < orient (point a) (point u) (point v) := by
  have hLu := hL u hu hua
  have hLv := hL v hv hva
  have hLne : L ≠ 0 := by intro hz; rw [hz] at hLu; simp at hLu
  exact slope_lt_orient L hLne (point a) (point u) (point v) hLu hLv he

theorem exists_key (Γ : Subgroup SL2) (p a : ℍ) (ha : a ∈ corners Γ p) :
    ∃ L : ℂ →L[ℝ] ℝ, (∀ z ∈ region Γ p, z ≠ a → L (point z) < L (point a)) ∧
      InjOn (key L a) (corners Γ p \ {a}) := by
  obtain ⟨L, hL⟩ := DirichletCornerExposure.exposed Γ p a ha
  exact ⟨L, hL, key_injective Γ p a ha L hL⟩

end VeechDichotomy.DirichletCornerSlopeOrder
