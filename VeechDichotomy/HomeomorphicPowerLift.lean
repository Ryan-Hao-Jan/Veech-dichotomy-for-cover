module

public import VeechDichotomy.TriangularPowerLift

/-! Power lifts for actual plane homeomorphisms whose angular ratios avoid
the negative-real cut. The inverse is computed from the inverse plane map.
Joint continuity in parameters is proved also at the ramification center. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HomeomorphicPowerLift

open Set Filter Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

def ratio (f : ℂ → ℂ) (z : ℂ) : ℂ := f z / z

def lift (f : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else z * (ratio f (z ^ k)) ^ (k⁻¹ : ℂ)

@[simp] theorem lift_zero (f : ℂ → ℂ) (k : ℕ) : lift f k 0 = 0 := by simp [lift]

theorem lift_pow (f : ℂ → ℂ) (hf0 : f 0 = 0) {k : ℕ} (hk : 0 < k) (z : ℂ) :
    lift f k z ^ k = f (z ^ k) := by
  by_cases hz : z = 0
  · subst z
    simp only [lift_zero, zero_pow hk.ne', hf0]
  · rw [lift, ite_eq_right hz, mul_pow, Complex.cpow_nat_inv_pow _ hk.ne']
    unfold ratio
    field_simp [pow_ne_zero k hz]

theorem lift_ne_zero (H : ℂ ≃ₜ ℂ) (hH0 : H 0 = 0) {k : ℕ} (hk : 0 < k) {z : ℂ} (hz : z ≠ 0) :
    lift H k z ≠ 0 := by
  intro heq
  have hp := lift_pow H hH0 hk z
  rw [heq, zero_pow hk.ne'] at hp
  exact pow_ne_zero k hz (H.injective (hp.symm.trans hH0.symm))

theorem lift_inverse_comp (H : ℂ ≃ₜ ℂ) (hH0 : H 0 = 0)
    (hslit : ∀ z ≠ 0, ratio H z ∈ Complex.slitPlane) {k : ℕ} (hk : 0 < k) (z : ℂ) :
    lift H.symm k (lift H k z) = z := by
  by_cases hz : z = 0
  · subst z
    rw [lift_zero, lift_zero]
  · have hw : z ^ k ≠ 0 := pow_ne_zero k hz
    have hratio : ratio H.symm (H (z ^ k)) = (ratio H (z ^ k))⁻¹ := by
      simp only [ratio, Homeomorph.symm_apply_apply, inv_div]
    have hHpow : H (z ^ k) ≠ 0 := fun h => hw (H.injective (h.trans hH0.symm))
    have hcpow : (ratio H (z ^ k)) ^ (k⁻¹ : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hHpow hw))
    calc
      lift H.symm k (lift H k z) = lift H k z * (ratio H.symm (lift H k z ^ k)) ^ (k⁻¹ : ℂ) :=
        ite_eq_right (lift_ne_zero H hH0 hk hz)
      _ = lift H k z * ((ratio H (z ^ k)) ^ (k⁻¹ : ℂ))⁻¹ := by
        rw [lift_pow H hH0 hk, hratio, Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi (hslit _ hw))]
      _ = z := by
        rw [lift, ite_eq_right hz, mul_assoc, mul_inv_cancel₀ hcpow, mul_one]

theorem continuousAt_of_power_zero {P : Type*} [PseudoMetricSpace P] {f : P → ℂ} {p : P}
    {k : ℕ} (hk : 0 < k) (hf0 : f p = 0) (hpow : ContinuousAt (fun q => f q ^ k) p) :
    ContinuousAt f p := by
  rw [Metric.continuousAt_iff] at hpow ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hpow (ε ^ k) (pow_pos hε k)
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have h := hbound hq
  rw [hf0, zero_pow hk.ne', dist_zero_right, norm_pow] at h
  simpa only [hf0, dist_zero_right] using lt_of_pow_lt_pow_left₀ k hε.le h

theorem continuous_family {P : Type*} [PseudoMetricSpace P] (H : P → ℂ ≃ₜ ℂ)
    (hH : Continuous (fun p : P × ℂ => H p.1 p.2)) (h0 : ∀ p, H p 0 = 0)
    (hslit : ∀ p z, z ≠ 0 → ratio (H p) z ∈ Complex.slitPlane) {k : ℕ} (hk : 0 < k) :
    Continuous (fun p : P × ℂ => lift (H p.1) k p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hz : p.2 = 0
  · apply continuousAt_of_power_zero hk (by simp only [hz, lift_zero])
    have heq : (fun q : P × ℂ => lift (H q.1) k q.2 ^ k) = fun q => H q.1 (q.2 ^ k) :=
      funext fun q => lift_pow _ (h0 q.1) hk q.2
    rw [heq]
    exact (hH.comp (continuous_fst.prodMk (continuous_snd.pow k))).continuousAt
  · have hr : ContinuousAt (fun q : P × ℂ => ratio (H q.1) (q.2 ^ k)) p :=
      ((hH.comp (continuous_fst.prodMk (continuous_snd.pow k))).continuousAt).div
        (continuous_snd.continuousAt.pow k) (pow_ne_zero k hz)
    have hp : ContinuousAt (fun q : P × ℂ => (ratio (H q.1) (q.2 ^ k)) ^ (k⁻¹ : ℂ)) p :=
      Filter.Tendsto.cpow hr tendsto_const_nhds (hslit p.1 _ (pow_ne_zero k hz))
    apply (continuous_snd.continuousAt.mul hp).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually_ne hz] with q hq
    exact ite_eq_right hq

theorem continuous_lift (H : ℂ ≃ₜ ℂ) (h0 : H 0 = 0)
    (hslit : ∀ z ≠ 0, ratio H z ∈ Complex.slitPlane) {k : ℕ} (hk : 0 < k) : Continuous (lift H k) := by
  have h := continuous_family (fun _ : Unit => H) (H.continuous.comp continuous_snd)
    (fun _ => h0) (fun _ => hslit) hk
  exact h.comp ((continuous_const : Continuous (fun _ : ℂ => ())).prodMk continuous_id)

def homeomorph (H : ℂ ≃ₜ ℂ) (h0 : H 0 = 0)
    (hslit : ∀ z ≠ 0, ratio H z ∈ Complex.slitPlane)
    (hInvSlit : ∀ z ≠ 0, ratio H.symm z ∈ Complex.slitPlane) (k : ℕ) (hk : 0 < k) : ℂ ≃ₜ ℂ where
  toFun := lift H k
  invFun := lift H.symm k
  left_inv := lift_inverse_comp H h0 hslit hk
  right_inv := by
    have hInv0 : H.symm 0 = 0 := by simpa only [h0] using H.symm_apply_apply 0
    exact lift_inverse_comp H.symm hInv0 hInvSlit hk
  continuous_toFun := continuous_lift H h0 hslit hk
  continuous_invFun := continuous_lift H.symm (by simpa only [h0] using H.symm_apply_apply 0) hInvSlit hk

end VeechDichotomy.HomeomorphicPowerLift
