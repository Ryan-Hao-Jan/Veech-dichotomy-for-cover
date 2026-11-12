module

public import Jacobians.LocalMultiplicity.AnalyticLocalFactorization
public import Jacobians.MappingDegree.AnalyticKthRoot
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! An unconditional local power normal form for a nonconstant analytic
function. The root substitution and the holomorphic coordinate are
constructed, not requested as certificate fields.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.AnalyticPowerCoordinate

open Set Filter Metric Topology Jacobians.Discharge.Manifold

theorem exists_power_coordinate {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (hnon : ¬ ∀ᶠ z in 𝓝 a, F z = F a) :
    ∃ k : ℕ, 0 < k ∧ ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e a = 0 ∧
      (∀ z ∈ e.source, F z - F a = (e z) ^ k) ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z) ∧
      (∀ z ∈ e.target, AnalyticAt ℂ e.symm z) := by
  classical
  have hg : AnalyticAt ℂ (fun z => F z - F a) a := hF.sub analyticAt_const
  have htop : analyticOrderAt (fun z => F z - F a) a ≠ ⊤ := by
    intro h
    apply hnon
    simpa only [sub_eq_zero] using (analyticOrderAt_eq_top.mp h)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    have horder0 : analyticOrderAt (fun z => F z - F a) a = 0 := by
      rw [← hk, hk0]
      rfl
    have hnonzero := (hg.analyticOrderAt_eq_zero).mp horder0
    exact hnonzero (sub_self (F a))
  obtain ⟨R, hR, u, hu, hua, hfactor⟩ :=
    analytic_local_factorization (Nat.one_le_iff_ne_zero.mpr hkpos.ne') hF rfl hk.symm
  obtain ⟨r, R', hR', hRR, hr, hroot⟩ :=
    analytic_kth_root_of_nonvanishing hR hu hua (Nat.one_le_iff_ne_zero.mpr hkpos.ne')
  let v : ℂ → ℂ := fun z => (z - a) * r z
  have hva : v a = 0 := by simp only [v, sub_self, zero_mul]
  have hra : AnalyticAt ℂ r a := hr a (mem_closedBall_self hR'.le)
  have hvan : AnalyticAt ℂ v a := (analyticAt_id.sub analyticAt_const).mul hra
  have hr0 : r a ≠ 0 := by
    intro h0
    have h := hroot a (mem_closedBall_self hR'.le)
    rw [h0, zero_pow hkpos.ne'] at h
    exact hua h.symm
  have hvd : HasDerivAt v (r a) a := by
    simpa only [v, id_eq, sub_self, zero_mul, one_mul, add_zero] using!
      (((hasDerivAt_id a).sub_const a).mul hra.differentiableAt.hasDerivAt)
  have hd : deriv v a ≠ 0 := by rw [hvd.deriv]; exact hr0
  have hfd := hvan.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  let e := hfd.toOpenPartialHomeomorph v
  have hcoe : (e : ℂ → ℂ) = v := hfd.toOpenPartialHomeomorph_coe
  have hsrc : a ∈ e.source := hfd.mem_toOpenPartialHomeomorph_source
  have hea : e a = 0 := by rw [hcoe]; exact hva
  have hean : AnalyticAt ℂ e a := by rw [hcoe]; exact hvan
  have heinv : AnalyticAt ℂ e.symm (e a) := by
    rw [hcoe]
    exact hvan.analyticAt_localInverse hd
  have hpow : ∀ᶠ z in 𝓝 a, F z - F a = (e z) ^ k := by
    filter_upwards [ball_mem_nhds a hR'] with z hz
    have hzclosed := ball_subset_closedBall hz
    have hzR : z ∈ closedBall a R := closedBall_subset_closedBall hRR hzclosed
    rw [hfactor z hzR, hcoe]
    change (z - a) ^ k * u z = ((z - a) * r z) ^ k
    rw [mul_pow, hroot z hzclosed]
  have hinvnear : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ e.symm (e z) :=
    (e.continuousAt hsrc) heinv.eventually_analyticAt
  have hnear : ∀ᶠ z in 𝓝 a, z ∈ e.source ∧ F z - F a = (e z) ^ k ∧
      AnalyticAt ℂ e z ∧ AnalyticAt ℂ e.symm (e z) := by
    filter_upwards [e.open_source.mem_nhds hsrc, hpow, hean.eventually_analyticAt,
      hinvnear] with z hs hp he hi
    exact ⟨hs, hp, he, hi⟩
  obtain ⟨U, hUsub, hU, haU⟩ := _root_.mem_nhds_iff.mp hnear
  let E := e.restr U
  have haE : a ∈ E.source := ⟨hsrc, by rwa [hU.interior_eq]⟩
  refine ⟨k, hkpos, E, haE, hea, ?_, ?_, ?_⟩
  · intro z hz
    exact (hUsub (interior_subset hz.2)).2.1
  · intro z hz
    exact (hUsub (interior_subset hz.2)).2.2.1
  · intro z hz
    have hs := E.map_target hz
    have h := (hUsub (interior_subset hs.2)).2.2.2
    have hez : e (E.symm z) = z := E.right_inv hz
    rwa [hez] at h

end VeechDichotomy.AnalyticPowerCoordinate
