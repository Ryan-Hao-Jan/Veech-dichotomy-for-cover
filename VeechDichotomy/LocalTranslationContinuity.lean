module

public import VeechDichotomy.LocalTranslationPlane

/-! Uniform estimates for the actual plane point transports, including
joint continuity of the inverse and its holomorphic translation germ.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.LocalTranslationContinuity

open Set Filter Metric Topology LocalTranslationPlane

set_option backward.isDefEq.respectTransparency false

theorem move_lower_bound {δ : ℂ} (hδ : ‖δ‖ < 1 / 2) (x y : ℂ) :
    dist x y ≤ 2 * dist (move δ x) (move δ y) := by
  have h := approximates hδ x (mem_univ _) y (mem_univ _)
  change ‖move δ x - move δ y - (x - y)‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ at h
  have ht := norm_sub_le (move δ x - move δ y) (move δ x - move δ y - (x - y))
  have heq : move δ x - move δ y - (move δ x - move δ y - (x - y)) = x - y := by abel
  rw [heq] at ht
  simp only [dist_eq_norm]
  linarith

theorem move_parameter_bound (δ ε z : ℂ) : dist (move δ z) (move ε z) ≤ dist δ ε := by
  have heq : move δ z - move ε z = cutoff z • (δ - ε) := by
    unfold move
    rw [smul_sub]
    abel
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg z)]
  calc
    cutoff z * ‖δ - ε‖ ≤ 1 * ‖δ - ε‖ := mul_le_mul_of_nonneg_right (cutoff_le_one z) (norm_nonneg _)
    _ = dist δ ε := by rw [one_mul, dist_eq_norm]

theorem inverse_joint_bound (δ ε : Parameter) (u v : ℂ) :
    dist ((homeomorph δ).symm u) ((homeomorph ε).symm v) ≤
      2 * (dist u v + dist δ.val ε.val) := by
  have hl := move_lower_bound δ.property ((homeomorph δ).symm u) ((homeomorph ε).symm v)
  have hu : move δ.val ((homeomorph δ).symm u) = u := (homeomorph δ).apply_symm_apply u
  have hv : move ε.val ((homeomorph ε).symm v) = v := (homeomorph ε).apply_symm_apply v
  rw [hu] at hl
  have hp := move_parameter_bound ε.val δ.val ((homeomorph ε).symm v)
  rw [hv, dist_comm ε.val δ.val] at hp
  have ht := dist_triangle u v (move δ.val ((homeomorph ε).symm v))
  linarith

theorem lipschitz_inverse : LipschitzWith 4 (fun p : Parameter × ℂ => (homeomorph p.1).symm p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := inverse_joint_bound p.1 q.1 p.2 q.2
  have hfst : dist p.1.val q.1.val ≤ dist p q := by
    change dist p.1 q.1 ≤ dist p q
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hsnd : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  change dist ((homeomorph p.1).symm p.2) ((homeomorph q.1).symm q.2) ≤ 4 * dist p q
  linarith

theorem continuous_forward : Continuous (fun p : Parameter × ℂ => homeomorph p.1 p.2) :=
  continuous_move.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem continuous_inverse : Continuous (fun p : Parameter × ℂ => (homeomorph p.1).symm p.2) :=
  lipschitz_inverse.continuous

theorem inverse_translation_germ (δ : Parameter) :
    ∀ᶠ z in 𝓝 δ.val, (homeomorph δ).symm z = z - δ.val := by
  have h0 : (homeomorph δ).symm δ.val = 0 := by
    rw [← homeomorph_origin δ]
    exact (homeomorph δ).symm_apply_apply 0
  have hball : ball (0 : ℂ) 1 ∈ 𝓝 ((homeomorph δ).symm δ.val) := by
    rw [h0]
    exact ball_mem_nhds _ (by norm_num)
  have hnear := (homeomorph δ).symm.continuous.continuousAt hball
  filter_upwards [hnear] with z hz
  have hn : ‖(homeomorph δ).symm z‖ ≤ 1 := by
    have hlt : ‖(homeomorph δ).symm z‖ < 1 := by
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hz
    exact hlt.le
  have ht := move_translation hn δ.val
  apply (eq_sub_iff_add_eq).mpr
  exact ht.symm.trans ((homeomorph δ).apply_symm_apply z)

theorem preserves_target (δ : Parameter) {T : Set ℂ} (hT : closedBall 0 2 ⊆ T)
    {z : ℂ} (hz : z ∈ T) : homeomorph δ z ∈ T := by
  by_cases hn : ‖z‖ < 2
  · apply hT
    simpa only [mem_closedBall, dist_zero_right] using (homeomorph_norm_lt_two δ hn).le
  · rw [homeomorph_fixed δ (le_of_not_gt hn)]
    exact hz

theorem inverse_preserves_target (δ : Parameter) {T : Set ℂ} (hT : closedBall 0 2 ⊆ T)
    {z : ℂ} (hz : z ∈ T) : (homeomorph δ).symm z ∈ T := by
  by_cases hn : ‖z‖ < 2
  · apply hT
    simpa only [mem_closedBall, dist_zero_right] using (inverse_norm_lt_two δ hn).le
  · rw [inverse_fixed δ (le_of_not_gt hn)]
    exact hz

end VeechDichotomy.LocalTranslationContinuity
