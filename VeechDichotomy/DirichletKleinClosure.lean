module

public import VeechDichotomy.NativeDirichletFiniteIdealBoundary

/-! The literal Euclidean closure of an actual Klein Dirichlet region
is compact and convex. Its open-disk part is exactly the actual region,
so every additional closure point lies on the actual ideal boundary. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletKleinClosure

open LinearGroup Set HyperbolicDirichletRegions HyperbolicKleinMap
open HyperbolicKleinHalfPlanes DirichletIdealRadialPoints
open scoped UpperHalfPlane

def closedRegion (Γ : Subgroup SL2) (p : ℍ) : Set ℂ := closure (point '' region Γ p)

theorem subset_closedBall (Γ : Subgroup SL2) (p : ℍ) : closedRegion Γ p ⊆ Metric.closedBall 0 1 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  rintro _ ⟨z, _, rfl⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using (norm_point_lt_one z).le

theorem norm_le (Γ : Subgroup SL2) (p : ℍ) {u : ℂ} (hu : u ∈ closedRegion Γ p) : ‖u‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using subset_closedBall Γ p hu

theorem isCompact_closedRegion (Γ : Subgroup SL2) (p : ℍ) : IsCompact (closedRegion Γ p) :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure (subset_closedBall Γ p)

theorem convex_closedRegion (Γ : Subgroup SL2) (p : ℍ) : Convex ℝ (closedRegion Γ p) :=
  (HyperbolicKleinDirichlet.convex_image_region Γ p).closure

theorem mem_image_of_norm_lt (Γ : Subgroup SL2) (p : ℍ) {u : ℂ}
    (hu : u ∈ closedRegion Γ p) (hn : ‖u‖ < 1) : u ∈ point '' region Γ p := by
  rw [HyperbolicKleinDirichlet.image_region]
  refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hn, ?_⟩
  exact mem_iInter.mpr (fun γ => closure_halfPlane Γ p hu γ)

theorem image_region_eq (Γ : Subgroup SL2) (p : ℍ) :
    point '' region Γ p = closedRegion Γ p ∩ Metric.ball 0 1 := by
  apply Subset.antisymm
  · intro u hu
    refine ⟨subset_closure hu, ?_⟩
    obtain ⟨z, _, rfl⟩ := hu
    simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one z
  · intro u hu
    exact mem_image_of_norm_lt Γ p hu.1 (by simpa only [Metric.mem_ball, dist_zero_right] using hu.2)

theorem mem_or_ideal (Γ : Subgroup SL2) (p : ℍ) {u : ℂ} (hu : u ∈ closedRegion Γ p) :
    u ∈ point '' region Γ p ∨ u ∈ idealBoundary Γ p := by
  rcases lt_or_eq_of_le (norm_le Γ p hu) with hn | hn
  · exact Or.inl (mem_image_of_norm_lt Γ p hu hn)
  · exact Or.inr ⟨hu, hn⟩

end VeechDichotomy.DirichletKleinClosure
