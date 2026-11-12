module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

/-! The actual real-linear maps z -> z + mu * conj z on the complex
unit disk of parameters, with explicit inverses and joint continuity.
Both forward and inverse angular ratios stay in the right half-plane. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiPlane

open Set Filter Topology

set_option backward.isDefEq.respectTransparency false

abbrev Parameter := {μ : ℂ // ‖μ‖ < 1}

def map (μ z : ℂ) : ℂ := z + μ * star z

def denominator (μ : ℂ) : ℂ := 1 - μ * star μ

theorem denominator_real (μ : ℂ) : denominator μ = ((1 - ‖μ‖ ^ 2 : ℝ) : ℂ) := by
  change 1 - μ * (starRingEnd ℂ) μ = ((1 - ‖μ‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.mul_conj']
  norm_cast

theorem denominator_pos (μ : Parameter) : 0 < 1 - ‖μ.val‖ ^ 2 := by
  have h := μ.property
  have hn := norm_nonneg μ.val
  nlinarith

theorem denominator_ne_zero (μ : Parameter) : denominator μ.val ≠ 0 := by
  rw [denominator_real]
  exact Complex.ofReal_ne_zero.mpr (denominator_pos μ).ne'

theorem conj_denominator (μ : ℂ) : star (denominator μ) = denominator μ := by
  rw [denominator_real]
  exact Complex.conj_ofReal _

def inverseMap (μ z : ℂ) : ℂ := (z - μ * star z) / denominator μ

@[simp] theorem map_zero (μ : ℂ) : map μ 0 = 0 := by simp [map]
@[simp] theorem inverseMap_zero (μ : ℂ) : inverseMap μ 0 = 0 := by simp [inverseMap]

theorem inverse_map_map (μ : Parameter) (z : ℂ) : inverseMap μ.val (map μ.val z) = z := by
  unfold inverseMap map
  rw [star_add, star_mul, star_star]
  apply (div_eq_iff (denominator_ne_zero μ)).mpr
  unfold denominator
  ring

theorem map_inverse_map (μ : Parameter) (z : ℂ) : map μ.val (inverseMap μ.val z) = z := by
  unfold map inverseMap
  rw [star_div₀, star_sub, star_mul, star_star, conj_denominator]
  field_simp [denominator_ne_zero μ]
  unfold denominator
  ring

def homeomorph (μ : Parameter) : ℂ ≃ₜ ℂ where
  toFun := map μ.val
  invFun := inverseMap μ.val
  left_inv := inverse_map_map μ
  right_inv := map_inverse_map μ
  continuous_toFun := by unfold map; fun_prop
  continuous_invFun := by unfold inverseMap; fun_prop

theorem continuous_forward : Continuous (fun p : Parameter × ℂ => homeomorph p.1 p.2) := by
  change Continuous (fun p : Parameter × ℂ => map p.1.val p.2)
  unfold map
  fun_prop

theorem continuous_inverse : Continuous (fun p : Parameter × ℂ => (homeomorph p.1).symm p.2) := by
  change Continuous (fun p : Parameter × ℂ => inverseMap p.1.val p.2)
  unfold inverseMap
  apply Continuous.div
  · fun_prop
  · unfold denominator
    fun_prop
  · intro p
    exact denominator_ne_zero p.1

theorem ratio_re_pos (μ : Parameter) {z : ℂ} (hz : z ≠ 0) : 0 < (map μ.val z / z).re := by
  have hr : map μ.val z / z = 1 + μ.val * star z / z := by
    rw [map, add_div, div_self hz]
  have hn : ‖μ.val * star z / z‖ = ‖μ.val‖ := by
    rw [norm_div, norm_mul, norm_star, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hz)]
  have hnorm := Complex.abs_re_le_norm (μ.val * star z / z)
  rw [hn] at hnorm
  have hlower := neg_abs_le (μ.val * star z / z).re
  rw [hr, Complex.add_re, Complex.one_re]
  have hμ := μ.property
  linarith

theorem ratio_slitPlane (μ : Parameter) {z : ℂ} (hz : z ≠ 0) : map μ.val z / z ∈ Complex.slitPlane :=
  Or.inl (ratio_re_pos μ hz)

theorem inverse_ratio_re_pos (μ : Parameter) {z : ℂ} (hz : z ≠ 0) : 0 < (inverseMap μ.val z / z).re := by
  let ν : Parameter := ⟨-μ.val, by simpa only [norm_neg] using μ.property⟩
  have hr : inverseMap μ.val z / z = (map ν.val z / z) / denominator μ.val := by
    unfold inverseMap map
    dsimp only [ν]
    ring
  rw [hr, denominator_real]
  have hreal : ((map ν.val z / z) / ((1 - ‖μ.val‖ ^ 2 : ℝ) : ℂ)).re =
      (map ν.val z / z).re / (1 - ‖μ.val‖ ^ 2) := by
    exact Complex.div_ofReal_re (map ν.val z / z) (1 - ‖μ.val‖ ^ 2)
  rw [hreal]
  exact div_pos (ratio_re_pos ν hz) (denominator_pos μ)

theorem inverse_ratio_slitPlane (μ : Parameter) {z : ℂ} (hz : z ≠ 0) : inverseMap μ.val z / z ∈ Complex.slitPlane :=
  Or.inl (inverse_ratio_re_pos μ hz)

end VeechDichotomy.BeltramiPlane
