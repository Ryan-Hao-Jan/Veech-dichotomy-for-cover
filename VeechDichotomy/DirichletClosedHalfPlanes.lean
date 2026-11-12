module

public import VeechDichotomy.DirichletCompactTruncations

/-! The actual closed Klein Dirichlet region is exactly the closed
disk intersected with all actual closed distance half-planes. At unit
points the reverse inclusion is proved by genuine radial points in
the actual region, so no boundary regularity is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletClosedHalfPlanes

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicKleinMap
open HyperbolicKleinHalfPlanes DirichletIdealRadialPoints IdealRadialLimits DirichletKleinClosure
open scoped UpperHalfPlane

theorem radialPoint_mem_of_halfPlanes (Γ : Subgroup SL2) (p : ℍ) {u : ℂ} (hu : ‖u‖ = 1)
    (hhalf : ∀ γ : Γ, affineForm p (γ • p) u ≤ 0) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    radialPoint p u hu t ht₀ ht₁ ∈ region Γ p := by
  intro γ
  apply (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) _).mpr
  rw [point_radialPoint]
  have hp := (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) p).mp (center_mem Γ p γ)
  exact (convex_halfPlane p (γ • p)) hp (hhalf γ) (sub_nonneg.mpr ht₁.le) ht₀ (by ring)

theorem idealBoundary_iff (Γ : Subgroup SL2) (p : ℍ) (u : ℂ) :
    u ∈ idealBoundary Γ p ↔ ‖u‖ = 1 ∧ ∀ γ : Γ, affineForm p (γ • p) u ≤ 0 := by
  constructor
  · exact fun hu => ⟨hu.2, fun γ => closure_halfPlane Γ p hu.1 γ⟩
  · rintro ⟨hu, hhalf⟩
    refine ⟨?_, hu⟩
    apply isClosed_closure.mem_of_tendsto (radial_tendsto p u)
    apply Eventually.of_forall
    intro k
    exact subset_closure ⟨approx p u hu k, radialPoint_mem_of_halfPlanes Γ p hu hhalf _ _ _, point_approx p u hu k⟩

theorem closedRegion_eq (Γ : Subgroup SL2) (p : ℍ) :
    closedRegion Γ p = Metric.closedBall 0 1 ∩ ⋂ γ : Γ, {u : ℂ | affineForm p (γ • p) u ≤ 0} := by
  apply Subset.antisymm
  · intro u hu
    exact ⟨subset_closedBall Γ p hu, mem_iInter.mpr (fun γ => closure_halfPlane Γ p hu γ)⟩
  · intro u hu
    have hn : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu.1
    rcases lt_or_eq_of_le hn with hn | hn
    · apply subset_closure
      rw [HyperbolicKleinDirichlet.image_region]
      exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hn, hu.2⟩
    · exact ((idealBoundary_iff Γ p u).mpr ⟨hn, fun γ => mem_iInter.mp hu.2 γ⟩).1

end VeechDichotomy.DirichletClosedHalfPlanes
