module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! Actual compactly supported plane homeomorphisms moving the origin.
They are translations on the unit disk and the identity outside radius2.
Invertibility is proved by a uniform contraction estimate, not supplied
as point-transport data. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.LocalTranslationPlane

open Set Metric Topology

set_option backward.isDefEq.respectTransparency false

def cutoff (z : ℂ) : ℝ := min 1 (max 0 (2 - ‖z‖))

theorem cutoff_nonneg (z : ℂ) : 0 ≤ cutoff z := le_min (by norm_num) (le_max_left _ _)

theorem cutoff_le_one (z : ℂ) : cutoff z ≤ 1 := min_le_left _ _

theorem cutoff_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1) : cutoff z = 1 := by
  apply min_eq_left
  apply (le_max_right _ _).trans'
  linarith

theorem cutoff_eq_zero {z : ℂ} (hz : 2 ≤ ‖z‖) : cutoff z = 0 := by
  unfold cutoff
  rw [max_eq_left (by linarith)]
  norm_num

theorem lipschitz_cutoff : LipschitzWith 1 cutoff := by
  have hraw : LipschitzWith 1 (fun z : ℂ => 2 - ‖z‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hn := lipschitzWith_one_norm.dist_le_mul x y
    have heq : dist (2 - ‖x‖) (2 - ‖y‖) = dist ‖x‖ ‖y‖ := by
      simp only [Real.dist_eq]
      rw [show 2 - ‖x‖ - (2 - ‖y‖) = -(‖x‖ - ‖y‖) by ring, abs_neg]
    rw [heq]
    exact hn
  exact (hraw.const_max 0).const_min 1

def move (δ z : ℂ) : ℂ := z + cutoff z • δ

theorem move_translation {z : ℂ} (hz : ‖z‖ ≤ 1) (δ : ℂ) : move δ z = z + δ := by
  rw [move, cutoff_eq_one hz, one_smul]

theorem move_fixed {z : ℂ} (hz : 2 ≤ ‖z‖) (δ : ℂ) : move δ z = z := by
  rw [move, cutoff_eq_zero hz, zero_smul, add_zero]

theorem continuous_move : Continuous (fun p : ℂ × ℂ => move p.1 p.2) :=
  continuous_snd.add ((lipschitz_cutoff.continuous.comp continuous_snd).smul continuous_fst)

theorem approximates {δ : ℂ} (hδ : ‖δ‖ < 1 / 2) :
    ApproximatesLinearOn (move δ) (ContinuousLinearMap.id ℝ ℂ) univ (1 / 2) := by
  intro x _ y _
  have heq : move δ x - move δ y - (x - y) = (cutoff x - cutoff y) • δ := by
    unfold move
    rw [sub_smul]
    abel
  change ‖move δ x - move δ y - (x - y)‖ ≤ (1 / 2 : ℝ) * ‖x - y‖
  rw [heq, norm_smul, Real.norm_eq_abs]
  have hcut : |cutoff x - cutoff y| ≤ ‖x - y‖ := by
    simpa only [Real.dist_eq, one_mul, NNReal.coe_one, dist_eq_norm, Real.norm_eq_abs] using lipschitz_cutoff.dist_le_mul x y
  calc
    |cutoff x - cutoff y| * ‖δ‖ ≤ ‖x - y‖ * (1 / 2) :=
      mul_le_mul hcut hδ.le (norm_nonneg _) (norm_nonneg _)
    _ = (1 / 2 : ℝ) * ‖x - y‖ := mul_comm _ _

abbrev Parameter := {δ : ℂ // ‖δ‖ < 1 / 2}

def homeomorph (δ : Parameter) : ℂ ≃ₜ ℂ :=
  (approximates δ.property).toHomeomorph (move δ.val)
    (f' := ContinuousLinearEquiv.refl ℝ ℂ) (Or.inr (by norm_num))

@[simp] theorem homeomorph_apply (δ : Parameter) (z : ℂ) : homeomorph δ z = move δ.val z := rfl

@[simp] theorem homeomorph_origin (δ : Parameter) : homeomorph δ 0 = δ.val := by
  rw [homeomorph_apply, move_translation (by norm_num), zero_add]

theorem homeomorph_fixed (δ : Parameter) {z : ℂ} (hz : 2 ≤ ‖z‖) : homeomorph δ z = z := move_fixed hz δ.val

theorem inverse_fixed (δ : Parameter) {z : ℂ} (hz : 2 ≤ ‖z‖) : (homeomorph δ).symm z = z := by
  have h := (homeomorph δ).symm_apply_apply z
  rwa [homeomorph_fixed δ hz] at h

theorem homeomorph_norm_lt_two (δ : Parameter) {z : ℂ} (hz : ‖z‖ < 2) : ‖homeomorph δ z‖ < 2 := by
  by_contra hn
  have hge : 2 ≤ ‖homeomorph δ z‖ := le_of_not_gt hn
  have hfix := homeomorph_fixed δ hge
  have heq : homeomorph δ z = z := (homeomorph δ).injective hfix
  rw [heq] at hge
  exact (not_lt_of_ge hge) hz

theorem inverse_norm_lt_two (δ : Parameter) {z : ℂ} (hz : ‖z‖ < 2) : ‖(homeomorph δ).symm z‖ < 2 := by
  by_contra hn
  have hge : 2 ≤ ‖(homeomorph δ).symm z‖ := le_of_not_gt hn
  have hfix := inverse_fixed δ hge
  have heq : (homeomorph δ).symm z = z := (homeomorph δ).symm.injective hfix
  rw [heq] at hge
  exact (not_lt_of_ge hge) hz

end VeechDichotomy.LocalTranslationPlane
