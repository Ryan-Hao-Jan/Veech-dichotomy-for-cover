module

public import MNEC.LatticeTorus
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Ring

/-!
# A continuous local translation extends across one straight line

The displacement along each off-line radial segment is locally constant
on the connected open interval. Continuity identifies its endpoint values.
Points on the line are then obtained by a transverse punctured approach.
Thus no equality of the translations on the two sides is assumed.
This is a standalone local lemma, not a flatness theorem about any surface.
-/

noncomputable section
@[expose] public section

namespace MNEC.RemovableTranslationLine

open LatticeTorus Set Filter Topology

def displacement (f : Plane → Plane) (p : Plane) : Plane := f p - p

theorem displacement_eventually_constant (f : Plane → Plane) (p : Plane)
    (hgerm : ∃ v : Plane, ∀ᶠ q in 𝓝 p, f q = q + v) :
    ∀ᶠ q in 𝓝 p, displacement f q = displacement f p := by
  obtain ⟨v, hv⟩ := hgerm
  have hp := hv.self_of_nhds
  filter_upwards [hv] with q hq
  simp [displacement, hq, hp]

theorem displacement_eq_center_off_line (f : Plane → Plane) (ℓ : Plane →L[ℝ] ℝ)
    (x : Plane) (U : Set Plane) (hU : Convex ℝ U) (hx : x ∈ U)
    (hf : ContinuousOn f U)
    (hloc : ∀ p ∈ U, ℓ (p - x) ≠ 0 → ∃ v : Plane, ∀ᶠ q in 𝓝 p, f q = q + v)
    (y : Plane) (hy : y ∈ U) (hline : ℓ (y - x) ≠ 0) :
    displacement f y = displacement f x := by
  let γ : ℝ → Plane := fun t => x + t • (y - x)
  let ψ : ℝ → Plane := fun t => displacement f (γ t)
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := fun t ht => hU.add_smul_sub_mem hx hy ht
  have hψ : ContinuousOn ψ (Icc (0 : ℝ) 1) :=
    (hf.sub continuousOn_id).comp hγ.continuousOn hpath
  have hsub : Continuous (fun t : Ioo (0 : ℝ) 1 => γ t.val) := hγ.comp continuous_subtype_val
  have hlc : IsLocallyConstant (fun t : Ioo (0 : ℝ) 1 => ψ t.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    have hpoint : γ t.val ∈ U := hpath t.val ⟨t.property.1.le, t.property.2.le⟩
    have hnonzero : ℓ (γ t.val - x) ≠ 0 := by
      have heq : ℓ (γ t.val - x) = t.val * ℓ (y - x) := by
        simp only [γ, add_sub_cancel_left, map_smul, smul_eq_mul]
      rw [heq]
      exact mul_ne_zero t.property.1.ne' hline
    exact hsub.continuousAt (displacement_eventually_constant f (γ t.val) (hloc _ hpoint hnonzero))
  let : PreconnectedSpace (Ioo (0 : ℝ) 1) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  let mid : Ioo (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  have hconst : ∀ t ∈ Ioo (0 : ℝ) 1, ψ t = ψ (1 / 2) := by
    intro t ht
    exact hlc.apply_eq_of_preconnectedSpace ⟨t, ht⟩ mid
  have hclosure : closure (Ioo (0 : ℝ) 1) = Icc (0 : ℝ) 1 := closure_Ioo zero_ne_one
  have hzero : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [hclosure]
    exact ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [hclosure]
    exact ⟨zero_le_one, le_rfl⟩
  have hcont0 : ContinuousWithinAt ψ (Ioo (0 : ℝ) 1) 0 :=
    (hψ 0 ⟨le_rfl, zero_le_one⟩).mono (fun _ ht => ⟨ht.1.le, ht.2.le⟩)
  have hcont1 : ContinuousWithinAt ψ (Ioo (0 : ℝ) 1) 1 :=
    (hψ 1 ⟨zero_le_one, le_rfl⟩).mono (fun _ ht => ⟨ht.1.le, ht.2.le⟩)
  have heq0 := hcont0.eq_const_of_mem_closure hzero hconst
  have heq1 := hcont1.eq_const_of_mem_closure hone hconst
  simpa [ψ, γ] using heq1.trans heq0.symm

theorem displacement_eq_center_on_ball (f : Plane → Plane) (ℓ : Plane →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (x : Plane) (r : ℝ) (hr : 0 < r)
    (hf : ContinuousOn f (Metric.ball x r))
    (hloc : ∀ p ∈ Metric.ball x r, ℓ (p - x) ≠ 0 →
      ∃ v : Plane, ∀ᶠ q in 𝓝 p, f q = q + v)
    (y : Plane) (hy : y ∈ Metric.ball x r) : displacement f y = displacement f x := by
  by_cases hline : ℓ (y - x) ≠ 0
  · exact displacement_eq_center_off_line f ℓ x _ (convex_ball x r) (Metric.mem_ball_self hr) hf hloc y hy hline
  · have hline0 : ℓ (y - x) = 0 := not_ne_iff.mp hline
    obtain ⟨v, hv⟩ : ∃ v : Plane, ℓ v ≠ 0 := by
      by_contra hn
      apply hℓ
      apply ContinuousLinearMap.ext
      intro v
      by_contra hv
      exact hn ⟨v, hv⟩
    let η : ℝ → Plane := fun s => y + s • v
    let δ : ℝ → Plane := fun s => displacement f (η s)
    have hη : Continuous η := continuous_const.add (continuous_id.smul continuous_const)
    have hη0 : η 0 = y := by simp [η]
    have hU : ∀ᶠ s in 𝓝 (0 : ℝ), η s ∈ Metric.ball x r := by
      apply hη.continuousAt
      simpa only [hη0] using Metric.isOpen_ball.mem_nhds hy
    have hfη : ContinuousAt f (η 0) := by
      rw [hη0]
      exact hf.continuousAt (Metric.isOpen_ball.mem_nhds hy)
    have hδ : ContinuousAt δ 0 := (hfη.comp hη.continuousAt).sub hη.continuousAt
    have hδlim : Tendsto δ (𝓝[≠] (0 : ℝ)) (𝓝 (displacement f y)) := by
      have ht : Tendsto δ (𝓝 (0 : ℝ)) (𝓝 (δ 0)) := hδ
      simpa only [δ, hη0] using ht.mono_left nhdsWithin_le_nhds
    have hδeq : δ =ᶠ[𝓝[≠] (0 : ℝ)] (fun _ => displacement f x) := by
      filter_upwards [hU.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hsU hs0
      have hsne : s ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hs0
      have heq : ℓ (η s - x) = s * ℓ v := by
        have hly : ℓ y = ℓ x := sub_eq_zero.mp (by simpa only [map_sub] using hline0)
        simp only [η, map_sub, map_add, map_smul, smul_eq_mul, hly]
        ring
      have hnonzero : ℓ (η s - x) ≠ 0 := by rw [heq]; exact mul_ne_zero hsne hv
      exact displacement_eq_center_off_line f ℓ x _ (convex_ball x r) (Metric.mem_ball_self hr)
        hf hloc (η s) hsU hnonzero
    exact tendsto_nhds_unique_of_eventuallyEq hδlim tendsto_const_nhds hδeq

/-- Continuity forces one translation on the entire ball, including the removed line. -/
theorem eq_translation_on_ball (f : Plane → Plane) (ℓ : Plane →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (x : Plane) (r : ℝ) (hr : 0 < r)
    (hf : ContinuousOn f (Metric.ball x r))
    (hloc : ∀ p ∈ Metric.ball x r, ℓ (p - x) ≠ 0 →
      ∃ v : Plane, ∀ᶠ q in 𝓝 p, f q = q + v) :
    ∀ y ∈ Metric.ball x r, f y = y + (f x - x) := by
  intro y hy
  have h := displacement_eq_center_on_ball f ℓ hℓ x r hr hf hloc y hy
  change f y - y = f x - x at h
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

theorem locally_translation_at_center (f : Plane → Plane) (ℓ : Plane →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (x : Plane) (r : ℝ) (hr : 0 < r)
    (hf : ContinuousOn f (Metric.ball x r))
    (hloc : ∀ p ∈ Metric.ball x r, ℓ (p - x) ≠ 0 →
      ∃ v : Plane, ∀ᶠ q in 𝓝 p, f q = q + v) :
    ∃ v : Plane, ∀ᶠ q in 𝓝 x, f q = q + v := by
  refine ⟨f x - x, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with y hy
  exact eq_translation_on_ball f ℓ hℓ x r hr hf hloc y hy

end MNEC.RemovableTranslationLine

