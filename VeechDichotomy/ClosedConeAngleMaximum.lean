module

public import VeechDichotomy.DirichletPointedCones
public import Mathlib.Topology.Order.Compact

/-! A genuine closed nonnegative complex cone with a nonzero vector
attains its angular width on its compact unit-direction set. If it is
pointed, that actual maximum is strictly below pi: equality would put
a vector and its negative in the cone. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ClosedConeAngleMaximum

open Set HyperbolicRegionAngles DirichletPointedCones

def unitSlice (K : Set ℂ) : Set ℂ := {u | u ∈ K ∧ ‖u‖ = 1}
def normalized (u : ℂ) : ℂ := (‖u‖⁻¹ : ℝ) • u

theorem unit_ne_zero {K : Set ℂ} {u : ℂ} (hu : u ∈ unitSlice K) : u ≠ 0 :=
  norm_pos_iff.mp (by rw [hu.2]; exact zero_lt_one)

theorem normalized_norm {u : ℂ} (hu : u ≠ 0) : ‖normalized u‖ = 1 := by
  rw [normalized, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hu)),
    inv_mul_cancel₀ (norm_pos_iff.mpr hu).ne']

theorem normalized_mem {K : Set ℂ}
    (hsmul : ∀ u : ℂ, u ∈ K → ∀ t : ℝ, 0 ≤ t → t • u ∈ K) {u : ℂ} (hu : u ∈ K) (hne : u ≠ 0) :
    normalized u ∈ unitSlice K :=
  ⟨hsmul u hu _ (inv_nonneg.mpr (norm_nonneg u)), normalized_norm hne⟩

theorem normalized_angle {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    InnerProductGeometry.angle (normalized u) (normalized v) = InnerProductGeometry.angle u v := by
  rw [normalized, normalized, InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hu)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr (norm_pos_iff.mpr hv))]

theorem isCompact_unitSlice {K : Set ℂ} (hK : IsClosed K) : IsCompact (unitSlice K) := by
  have he : unitSlice K = Metric.sphere (0 : ℂ) 1 ∩ K := by
    ext u
    simp only [unitSlice, mem_ofPred_eq, mem_inter_iff, Metric.mem_sphere, dist_zero_right]
    exact and_comm
  rw [he]
  exact (isCompact_sphere (0 : ℂ) 1).inter_right hK

theorem maximum {K : Set ℂ} (hK : IsClosed K)
    (hsmul : ∀ u : ℂ, u ∈ K → ∀ t : ℝ, 0 ≤ t → t • u ∈ K)
    (hne : ∃ u : ℂ, u ∈ K ∧ u ≠ 0) :
    ∃ u v : ℂ, u ∈ unitSlice K ∧ v ∈ unitSlice K ∧ vectorWidth K = InnerProductGeometry.angle u v := by
  obtain ⟨w, hw, hwne⟩ := hne
  have hunit : (unitSlice K).Nonempty := ⟨normalized w, normalized_mem hsmul hw hwne⟩
  have hc : IsCompact (unitSlice K ×ˢ unitSlice K) := (isCompact_unitSlice hK).prod (isCompact_unitSlice hK)
  have hcont : ContinuousOn (fun q : ℂ × ℂ => InnerProductGeometry.angle q.1 q.2) (unitSlice K ×ˢ unitSlice K) := by
    intro q hq
    exact (InnerProductGeometry.continuousAt_angle (unit_ne_zero hq.1) (unit_ne_zero hq.2)).continuousWithinAt
  obtain ⟨q, hq, hmax⟩ := hc.exists_isMaxOn (hunit.prod hunit) hcont
  refine ⟨q.1, q.2, hq.1, hq.2, le_antisymm ?_ ?_⟩
  · apply csSup_le (vectorValues_nonempty K)
    rintro θ (hz | ⟨u, v, hu, hv, hune, hvne, rfl⟩)
    · have he : θ = 0 := hz
      rw [he]
      exact InnerProductGeometry.angle_nonneg _ _
    · have hpair : (normalized u, normalized v) ∈ unitSlice K ×ˢ unitSlice K :=
        ⟨normalized_mem hsmul hu hune, normalized_mem hsmul hv hvne⟩
      have h := @hmax (normalized u, normalized v) hpair
      change InnerProductGeometry.angle (normalized u) (normalized v) ≤ InnerProductGeometry.angle q.1 q.2 at h
      rwa [normalized_angle hune hvne] at h
  · exact le_csSup (vectorValues_bddAbove K)
      (Or.inr ⟨q.1, q.2, hq.1.1, hq.2.1, unit_ne_zero hq.1, unit_ne_zero hq.2, rfl⟩)

theorem width_lt_pi {K : Set ℂ} (hK : IsClosed K)
    (hsmul : ∀ u : ℂ, u ∈ K → ∀ t : ℝ, 0 ≤ t → t • u ∈ K)
    (hne : ∃ u : ℂ, u ∈ K ∧ u ≠ 0) (hpointed : Pointed K) : vectorWidth K < Real.pi := by
  obtain ⟨u, v, hu, hv, hwidth⟩ := maximum hK hsmul hne
  have hnot : InnerProductGeometry.angle u v ≠ Real.pi := by
    intro he
    obtain ⟨_, r, hr, hvr⟩ := InnerProductGeometry.angle_eq_pi_iff.mp he
    have hnegv : -v ∈ K := by
      rw [hvr, ← neg_smul]
      exact hsmul u hu.1 (-r) (neg_nonneg.mpr hr.le)
    exact unit_ne_zero hv (hpointed v hv.1 hnegv)
  rw [hwidth]
  exact lt_of_le_of_ne (InnerProductGeometry.angle_le_pi u v) hnot

end VeechDichotomy.ClosedConeAngleMaximum
