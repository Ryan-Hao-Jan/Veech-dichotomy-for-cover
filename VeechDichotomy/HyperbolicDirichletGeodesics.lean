module

public import VeechDichotomy.HyperbolicCommonGeodesic
public import VeechDichotomy.HyperbolicVerticalConvexity
public import VeechDichotomy.HyperbolicKleinSegments

/-! Actual constant-speed metric geodesic paths stay in genuine Dirichlet
regions. Each pair of endpoints is explicitly normalized to a vertical
geodesic, actual intermediate-clock distance comparisons are proved,
and actual isometries compute every pairwise path distance. No abstract
geodesic/convexity hypothesis is left to be discharged. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletGeodesics

open LinearGroup HyperbolicGeodesicLines HyperbolicCommonGeodesic HyperbolicVerticalConvexity
open HyperbolicDirichletRegions Set Topology
open scoped UpperHalfPlane unitInterval

set_option backward.isDefEq.respectTransparency false

def line (A : SL2) (c t : ℝ) : ℍ := A⁻¹ • verticalPoint c t

theorem line_isometry (A : SL2) (c : ℝ) : Isometry (line A c) :=
  (isometry_smul ℍ A⁻¹).comp (vertical_isometry c)

theorem line_distance (A : SL2) (c s t : ℝ) : dist (line A c s) (line A c t) = dist s t :=
  (line_isometry A c).dist_eq s t

theorem dist_to_point (A : SL2) (c t : ℝ) (p : ℍ) :
    dist (line A c t) p = dist (verticalPoint c t) (A • p) := by
  simpa only [line, smul_inv_smul] using (dist_smul A (A⁻¹ • verticalPoint c t) p).symm

theorem line_comparison_between (A : SL2) (c : ℝ) (p q : ℍ) (s₀ s₁ s : ℝ)
    (hs : s ∈ uIcc s₀ s₁) (h₀ : dist (line A c s₀) p ≤ dist (line A c s₀) q)
    (h₁ : dist (line A c s₁) p ≤ dist (line A c s₁) q) :
    dist (line A c s) p ≤ dist (line A c s) q := by
  simp only [dist_to_point] at h₀ h₁ ⊢
  exact comparison_between (A • p) (A • q) c s₀ s₁ s hs h₀ h₁

def clock (s₀ s₁ : ℝ) (t : I) : ℝ := (1 - t.val) * s₀ + t.val * s₁

theorem clock_between (s₀ s₁ : ℝ) (t : I) : clock s₀ s₁ t ∈ uIcc s₀ s₁ := by
  change (1 - t.val) • s₀ + t.val • s₁ ∈ uIcc s₀ s₁
  exact (convex_uIcc _ _) left_mem_uIcc right_mem_uIcc
    (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

def segment (A : SL2) (c s₀ s₁ : ℝ) (t : I) : ℍ := line A c (clock s₀ s₁ t)

theorem segment_continuous (A : SL2) (c s₀ s₁ : ℝ) : Continuous (segment A c s₀ s₁) := by
  have hc : Continuous (clock s₀ s₁) := by unfold clock; fun_prop
  exact (line_isometry A c).continuous.comp hc

@[simp] theorem segment_zero (A : SL2) (c s₀ s₁ : ℝ) : segment A c s₀ s₁ 0 = line A c s₀ := by
  simp [segment, clock]

@[simp] theorem segment_one (A : SL2) (c s₀ s₁ : ℝ) : segment A c s₀ s₁ 1 = line A c s₁ := by
  simp [segment, clock]

theorem segment_distance (A : SL2) (c s₀ s₁ : ℝ) (t u : I) :
    dist (segment A c s₀ s₁ t) (segment A c s₀ s₁ u) = |s₁ - s₀| * dist t.val u.val := by
  rw [segment, segment, line_distance, Real.dist_eq, Real.dist_eq]
  have heq : clock s₀ s₁ t - clock s₀ s₁ u = (s₁ - s₀) * (t.val - u.val) := by unfold clock; ring
  rw [heq, abs_mul]

theorem segment_mem_region (Γ : Subgroup SL2) (p : ℍ) (A : SL2) (c s₀ s₁ : ℝ)
    (h₀ : line A c s₀ ∈ region Γ p) (h₁ : line A c s₁ ∈ region Γ p) (t : I) :
    segment A c s₀ s₁ t ∈ region Γ p := by
  intro γ
  exact line_comparison_between A c p (γ • p) s₀ s₁ (clock s₀ s₁ t) (clock_between s₀ s₁ t) (h₀ γ) (h₁ γ)

theorem exists_geodesic_path (Γ : Subgroup SL2) (p a b : ℍ)
    (ha : a ∈ region Γ p) (hb : b ∈ region Γ p) :
    ∃ γ : Path a b, (∀ t, γ t ∈ region Γ p) ∧
      ∀ t u : I, dist (γ t) (γ u) = dist a b * dist t.val u.val := by
  obtain ⟨A, c, s₀, s₁, h₀, h₁⟩ := exists_clock_coordinates a b
  change line A c s₀ = a at h₀
  change line A c s₁ = b at h₁
  let γ : Path a b :=
    { toFun := segment A c s₀ s₁
      continuous_toFun := segment_continuous A c s₀ s₁
      source' := (segment_zero A c s₀ s₁).trans h₀
      target' := (segment_one A c s₀ s₁).trans h₁ }
  have hdist : dist a b = |s₁ - s₀| := by
    rw [← h₀, ← h₁, line_distance, Real.dist_eq, abs_sub_comm]
  refine ⟨γ, fun t => segment_mem_region Γ p A c s₀ s₁ (h₀.symm ▸ ha) (h₁.symm ▸ hb) t, ?_⟩
  intro t u
  change dist (segment A c s₀ s₁ t) (segment A c s₀ s₁ u) = dist a b * dist t.val u.val
  rw [segment_distance, hdist]

end VeechDichotomy.HyperbolicDirichletGeodesics
