module

public import VeechDichotomy.HyperbolicGeodesicLines
public import VeechDichotomy.HyperbolicDistanceComparison

/-! Actual distance half-plane comparisons remain true between two
vertical geodesic clocks. The exact distance polynomial is affine in
the monotone positive height variable exp(t)^2, so endpoint inequalities
bound every intermediate clock. This is a proved metric convexity fact. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicVerticalConvexity

open HyperbolicGeodesicLines HyperbolicDistanceComparison HyperbolicBisectorNull Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem affine_bound_between (A B x₀ x₁ x : ℝ) (h₀ : x₀ ≤ x) (h₁ : x ≤ x₁)
    (hf₀ : A * x₀ + B ≤ 0) (hf₁ : A * x₁ + B ≤ 0) : A * x + B ≤ 0 := by
  by_cases hA : 0 ≤ A
  · have hm := mul_le_mul_of_nonneg_left h₁ hA
    linarith only [hm, hf₁]
  · have hA' : A ≤ 0 := le_of_lt (lt_of_not_ge hA)
    have hm := mul_le_mul_of_nonpos_left h₀ hA'
    linarith only [hm, hf₀]

theorem height_monotone : Monotone (fun t : ℝ => Real.exp t ^ 2) := by
  intro s t hst
  exact pow_le_pow_left₀ (Real.exp_pos s).le (Real.exp_le_exp.mpr hst) 2

theorem vertical_form (p q : ℍ) (c t : ℝ) : form p q (verticalPoint c t) =
    leading p q * Real.exp t ^ 2 + (leading p q * c ^ 2 + linear p q * c + constant p q) := by
  simp only [form, verticalPoint, Complex.normSq_apply]
  ring

theorem comparison_ordered (p q : ℍ) (c s₀ s₁ s : ℝ) (hs₀ : s₀ ≤ s) (hs₁ : s ≤ s₁)
    (h₀ : dist (verticalPoint c s₀) p ≤ dist (verticalPoint c s₀) q)
    (h₁ : dist (verticalPoint c s₁) p ≤ dist (verticalPoint c s₁) q) :
    dist (verticalPoint c s) p ≤ dist (verticalPoint c s) q := by
  have hf₀ := (HyperbolicDistanceComparison.dist_le_iff p q (verticalPoint c s₀)).mp h₀
  have hf₁ := (HyperbolicDistanceComparison.dist_le_iff p q (verticalPoint c s₁)).mp h₁
  rw [vertical_form] at hf₀ hf₁
  apply (HyperbolicDistanceComparison.dist_le_iff p q (verticalPoint c s)).mpr
  rw [vertical_form]
  exact affine_bound_between _ _ _ _ _ (height_monotone hs₀) (height_monotone hs₁) hf₀ hf₁

theorem comparison_between (p q : ℍ) (c s₀ s₁ s : ℝ) (hs : s ∈ uIcc s₀ s₁)
    (h₀ : dist (verticalPoint c s₀) p ≤ dist (verticalPoint c s₀) q)
    (h₁ : dist (verticalPoint c s₁) p ≤ dist (verticalPoint c s₁) q) :
    dist (verticalPoint c s) p ≤ dist (verticalPoint c s) q := by
  rcases le_total s₀ s₁ with h | h
  · rw [uIcc_of_le h] at hs
    exact comparison_ordered p q c s₀ s₁ s hs.1 hs.2 h₀ h₁
  · rw [uIcc_of_ge h] at hs
    exact comparison_ordered p q c s₁ s₀ s hs.1 hs.2 h₁ h₀

end VeechDichotomy.HyperbolicVerticalConvexity
