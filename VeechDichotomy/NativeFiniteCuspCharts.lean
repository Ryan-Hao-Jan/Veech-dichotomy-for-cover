module

public import VeechDichotomy.RelativeIdealHoroballs

/-! Actual cusp charts are constructed for the finite set of actual
ideal endpoints. A single positive normalized depth works for every
chart's genuine strip and translation-separation bounds. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFiniteCuspCharts

open LinearGroup HyperbolicRegularCenters DirichletIdealRadialPoints HyperbolicDirichletRegions
open NativeLatticeConjugation
open scoped UpperHalfPlane

structure Chart (Γ : Subgroup SL2) (p : ℍ) (u : idealBoundary Γ p) where
  matrix : SL2
  endpoint_eq : SL2BottomRowEndpoints.endpoint matrix = u.val
  period : ℝ
  period_pos : 0 < period
  period_mem : IdealInfinityStabilizers.upper period ∈ conjugate Γ matrix
  left : ℝ
  right : ℝ
  height : ℝ
  left_lt : left < (matrix • p).re
  right_gt : (matrix • p).re < right
  height_pos : 0 < height
  strip : ∀ z : ℍ, height ≤ (matrix • z).im →
    (z ∈ region Γ p ↔ (matrix • z).re ∈ Set.Icc left right)

theorem chart_nonempty (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (u : idealBoundary Γ p) : Nonempty (Chart Γ p u) := by
  obtain ⟨B, τ, a, b, Y, he, hτ, hmem, ha, hb, hY, hstrip, _⟩ :=
    NativeIdealCuspCoordinates.exists_coordinates Γ hΓ p hp u.property
  exact ⟨⟨B, he, τ, hτ, hmem, a, b, Y, ha, hb, hY, hstrip⟩⟩

def chart (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (u : idealBoundary Γ p) : Chart Γ p u := Classical.choice (chart_nonempty Γ hΓ p hp u)

theorem exists_common_depth (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : idealBoundary Γ p,
      let c := chart Γ hΓ p hp u
      c.height ≤ R * (c.matrix • p).im ∧
        c.period ^ 2 + (c.matrix • p).im ^ 2 ≤ R ^ 2 * (c.matrix • p).im ^ 2 := by
  classical
  let : Finite (idealBoundary Γ p) := (NativeDirichletFiniteIdealBoundary.idealBoundary_finite Γ hΓ p).to_subtype
  let : Fintype (idealBoundary Γ p) := Fintype.ofFinite _
  let c := chart Γ hΓ p hp
  let W : idealBoundary Γ p → ℝ := fun u =>
    (c u).period / ((c u).matrix • p).im + (c u).height / ((c u).matrix • p).im + 1
  have hW (u : idealBoundary Γ p) : 0 ≤ W u := by
    dsimp only [W]
    exact add_nonneg (add_nonneg
      (div_pos (c u).period_pos ((c u).matrix • p).im_pos).le
      (div_pos (c u).height_pos ((c u).matrix • p).im_pos).le) zero_le_one
  let R : ℝ := 1 + ∑ u : idealBoundary Γ p, W u
  have hsum : 0 ≤ ∑ u : idealBoundary Γ p, W u := Finset.sum_nonneg (fun u _ => hW u)
  have hR : 0 < R := by dsimp only [R]; linarith only [hsum]
  refine ⟨R, hR, ?_⟩
  intro u
  have hw : W u ≤ R := by
    have hh : W u ≤ ∑ v : idealBoundary Γ p, W v :=
      Finset.single_le_sum (f := W) (fun v _ => hW v) (Finset.mem_univ u)
    dsimp only [R]
    linarith only [hh]
  change (c u).period / ((c u).matrix • p).im + (c u).height / ((c u).matrix • p).im + 1 ≤ R at hw
  have hper : 0 ≤ (c u).period / ((c u).matrix • p).im := (div_pos (c u).period_pos ((c u).matrix • p).im_pos).le
  have hhgt : 0 ≤ (c u).height / ((c u).matrix • p).im := (div_pos (c u).height_pos ((c u).matrix • p).im_pos).le
  have hH : (c u).height ≤ R * ((c u).matrix • p).im := by
    apply (div_le_iff₀ ((c u).matrix • p).im_pos).mp
    linarith only [hw, hper]
  have hbound : (c u).period + ((c u).matrix • p).im ≤ R * ((c u).matrix • p).im := by
    have hr : (c u).period / ((c u).matrix • p).im + 1 ≤ R := by linarith only [hw, hhgt]
    have hm := mul_le_mul_of_nonneg_right hr ((c u).matrix • p).im_pos.le
    simpa only [add_mul, div_mul_cancel₀ _ ((c u).matrix • p).im_ne_zero, one_mul] using hm
  have hs := (sq_le_sq₀ (add_pos (c u).period_pos ((c u).matrix • p).im_pos).le
    (mul_pos hR ((c u).matrix • p).im_pos).le).mpr hbound
  refine ⟨hH, ?_⟩
  nlinarith only [hs, mul_nonneg (c u).period_pos.le ((c u).matrix • p).im_pos.le]

end VeechDichotomy.NativeFiniteCuspCharts
