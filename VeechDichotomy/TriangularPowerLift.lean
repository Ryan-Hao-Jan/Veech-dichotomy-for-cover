module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

/-! Explicit homeomorphic lifts of positive triangular real-linear maps
through z -> z^k. This supplies a concrete local tool for deforming cone
coordinates. Branch continuity is proved via the slit-plane condition;
continuity at zero is proved from the power identity.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.TriangularPowerLift

open Set Filter Topology
open scoped Classical

structure PositiveTriangular where
  a : ℝ
  b : ℝ
  d : ℝ
  a_pos : 0 < a
  d_pos : 0 < d

def map (T : PositiveTriangular) (z : ℂ) : ℂ :=
  ⟨T.a * z.re + T.b * z.im, T.d * z.im⟩

@[simp] theorem map_zero (T : PositiveTriangular) : map T 0 = 0 := by
  apply Complex.ext <;> simp [map]

theorem continuous_map (T : PositiveTriangular) : Continuous (map T) := by
  have heq : map T = fun z : ℂ =>
      Complex.equivRealProdCLM.symm (T.a * z.re + T.b * z.im, T.d * z.im) := by
    funext z
    apply Complex.ext <;> simp [map, Complex.equivRealProdCLM_symm_apply]
  rw [heq]
  exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)

theorem map_ne_zero (T : PositiveTriangular) {z : ℂ} (hz : z ≠ 0) : map T z ≠ 0 := by
  intro h
  have hi : T.d * z.im = 0 := congrArg Complex.im h
  have hy : z.im = 0 := (mul_eq_zero.mp hi).resolve_left T.d_pos.ne'
  have hr : T.a * z.re = 0 := by
    simpa only [map, Complex.zero_re, hy, mul_zero, add_zero] using congrArg Complex.re h
  exact hz (Complex.ext ((mul_eq_zero.mp hr).resolve_left T.a_pos.ne') hy)

def inverse (T : PositiveTriangular) : PositiveTriangular where
  a := T.a⁻¹
  b := -T.b / (T.a * T.d)
  d := T.d⁻¹
  a_pos := inv_pos.mpr T.a_pos
  d_pos := inv_pos.mpr T.d_pos

theorem inverse_map_map (T : PositiveTriangular) (z : ℂ) : map (inverse T) (map T z) = z := by
  apply Complex.ext
  · change T.a⁻¹ * (T.a * z.re + T.b * z.im) + (-T.b / (T.a * T.d)) * (T.d * z.im) = z.re
    field_simp [T.a_pos.ne', T.d_pos.ne']
    ring
  · change T.d⁻¹ * (T.d * z.im) = z.im
    field_simp [T.d_pos.ne']

theorem map_inverse_map (T : PositiveTriangular) (z : ℂ) : map T (map (inverse T) z) = z := by
  apply Complex.ext
  · change T.a * (T.a⁻¹ * z.re + (-T.b / (T.a * T.d)) * z.im) + T.b * (T.d⁻¹ * z.im) = z.re
    field_simp [T.a_pos.ne', T.d_pos.ne']
    ring
  · change T.d * (T.d⁻¹ * z.im) = z.im
    field_simp [T.d_pos.ne']

def ratio (T : PositiveTriangular) (z : ℂ) : ℂ := map T z / z

theorem ratio_ne_zero (T : PositiveTriangular) {z : ℂ} (hz : z ≠ 0) : ratio T z ≠ 0 :=
  div_ne_zero (map_ne_zero T hz) hz

theorem ratio_mem_slitPlane (T : PositiveTriangular) {z : ℂ} (hz : z ≠ 0) :
    ratio T z ∈ Complex.slitPlane := by
  change 0 < (ratio T z).re ∨ (ratio T z).im ≠ 0
  by_cases hi : (ratio T z).im = 0
  · left
    by_contra hpos
    have hnonpos : (ratio T z).re ≤ 0 := le_of_not_gt hpos
    have hmul : ratio T z * z = map T z := div_mul_cancel₀ _ hz
    have him : (ratio T z).re * z.im = T.d * z.im := by
      simpa only [Complex.mul_im, hi, zero_mul, add_zero, map] using congrArg Complex.im hmul
    have hd : T.d - (ratio T z).re ≠ 0 := (sub_pos.mpr (hnonpos.trans_lt T.d_pos)).ne'
    have hy : z.im = 0 := (mul_eq_zero.mp (show (T.d - (ratio T z).re) * z.im = 0 by nlinarith)).resolve_left hd
    have hre : (ratio T z).re * z.re = T.a * z.re := by
      simpa only [Complex.mul_re, hi, hy, zero_mul, mul_zero, sub_zero, add_zero,
        map] using congrArg Complex.re hmul
    have ha : T.a - (ratio T z).re ≠ 0 := (sub_pos.mpr (hnonpos.trans_lt T.a_pos)).ne'
    have hx : z.re = 0 := (mul_eq_zero.mp (show (T.a - (ratio T z).re) * z.re = 0 by nlinarith)).resolve_left ha
    exact hz (Complex.ext hx hy)
  · exact Or.inr hi

def rootLift (T : PositiveTriangular) (k : ℕ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else z * (ratio T (z ^ k)) ^ (k⁻¹ : ℂ)

@[simp] theorem rootLift_zero (T : PositiveTriangular) (k : ℕ) : rootLift T k 0 = 0 := by
  simp [rootLift]

theorem rootLift_pow (T : PositiveTriangular) {k : ℕ} (hk : 0 < k) (z : ℂ) :
    (rootLift T k z) ^ k = map T (z ^ k) := by
  by_cases hz : z = 0
  · subst z
    simp only [rootLift_zero, zero_pow hk.ne', map_zero]
  · rw [rootLift, ite_eq_right hz, mul_pow, Complex.cpow_nat_inv_pow _ hk.ne']
    unfold ratio
    field_simp [pow_ne_zero k hz]

theorem rootLift_ne_zero (T : PositiveTriangular) {k : ℕ} (hk : 0 < k) {z : ℂ}
    (hz : z ≠ 0) : rootLift T k z ≠ 0 := by
  intro h
  have hp := rootLift_pow T hk z
  rw [h, zero_pow hk.ne'] at hp
  exact map_ne_zero T (pow_ne_zero k hz) hp.symm

theorem continuousAt_zero_of_continuous_power {f : ℂ → ℂ} {k : ℕ} (hk : 0 < k)
    (hf0 : f 0 = 0) (hpow : ContinuousAt (fun z => (f z) ^ k) 0) : ContinuousAt f 0 := by
  rw [Metric.continuousAt_iff] at hpow ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := hpow (ε ^ k) (pow_pos hε k)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have h := hδbound hz
  rw [hf0, zero_pow hk.ne', dist_zero_right, norm_pow] at h
  simpa only [hf0, dist_zero_right] using lt_of_pow_lt_pow_left₀ k hε.le h

theorem continuous_rootLift (T : PositiveTriangular) {k : ℕ} (hk : 0 < k) :
    Continuous (rootLift T k) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    apply continuousAt_zero_of_continuous_power hk (rootLift_zero T k)
    have heq : (fun z => rootLift T k z ^ k) = fun z => map T (z ^ k) := funext (rootLift_pow T hk)
    rw [heq]
    exact ((continuous_map T).comp (continuous_id.pow k)).continuousAt
  · have hc : ContinuousAt (fun w : ℂ => ratio T (w ^ k)) z :=
      ((continuous_map T).continuousAt.comp (continuousAt_id.pow k)).div
        (continuousAt_id.pow k) (pow_ne_zero k hz)
    have hcpow : ContinuousAt (fun w : ℂ => (ratio T (w ^ k)) ^ (k⁻¹ : ℂ)) z :=
      Filter.Tendsto.cpow hc tendsto_const_nhds (ratio_mem_slitPlane T (pow_ne_zero k hz))
    have hmain : ContinuousAt (fun w : ℂ => w * (ratio T (w ^ k)) ^ (k⁻¹ : ℂ)) z :=
      continuousAt_id.mul hcpow
    apply hmain.congr_of_eventuallyEq
    filter_upwards [continuousAt_id.eventually_ne hz] with w hw
    exact ite_eq_right hw

theorem rootLift_comp_of_leftInverse (S T : PositiveTriangular)
    (hST : ∀ z, map S (map T z) = z) {k : ℕ} (hk : 0 < k) (z : ℂ) :
    rootLift S k (rootLift T k z) = z := by
  by_cases hz : z = 0
  · subst z
    rw [rootLift_zero, rootLift_zero]
  · have hw : z ^ k ≠ 0 := pow_ne_zero k hz
    have hr : ratio S (map T (z ^ k)) = (ratio T (z ^ k))⁻¹ := by
      simp only [ratio, hST, inv_div]
    have hcpow : (ratio T (z ^ k)) ^ (k⁻¹ : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (ratio_ne_zero T hw))
    calc
      rootLift S k (rootLift T k z) = rootLift T k z *
          (ratio S (rootLift T k z ^ k)) ^ (k⁻¹ : ℂ) := ite_eq_right (rootLift_ne_zero T hk hz)
      _ = rootLift T k z * ((ratio T (z ^ k)) ^ (k⁻¹ : ℂ))⁻¹ := by
        rw [rootLift_pow T hk, hr, Complex.inv_cpow _ _
          (Complex.slitPlane_arg_ne_pi (ratio_mem_slitPlane T hw))]
      _ = z := by
        rw [rootLift, ite_eq_right hz, mul_assoc, mul_inv_cancel₀ hcpow, mul_one]

def rootHomeomorph (T : PositiveTriangular) (k : ℕ) (hk : 0 < k) : ℂ ≃ₜ ℂ where
  toFun := rootLift T k
  invFun := rootLift (inverse T) k
  left_inv := rootLift_comp_of_leftInverse (inverse T) T (inverse_map_map T) hk
  right_inv := rootLift_comp_of_leftInverse T (inverse T) (map_inverse_map T) hk
  continuous_toFun := continuous_rootLift T hk
  continuous_invFun := continuous_rootLift (inverse T) hk

theorem rootHomeomorph_pow (T : PositiveTriangular) (k : ℕ) (hk : 0 < k) (z : ℂ) :
    (rootHomeomorph T k hk z) ^ k = map T (z ^ k) := rootLift_pow T hk z

end VeechDichotomy.TriangularPowerLift
