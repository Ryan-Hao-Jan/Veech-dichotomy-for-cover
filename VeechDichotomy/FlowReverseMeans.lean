module

public import VeechDichotomy.KoopmanInverseMeans
public import VeechDichotomy.FlowContinuousProfiles

/-! Forward and backward continuous occupation means are the SAME
actual L2 vector. The reverse unit block is the inverse-time translate
of the forward block; inverse Koopman maps have the same fixed space
and their mean is unchanged by that translate. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FlowReverseMeans

open MeasureTheory Filter Topology FlowUnitBlock KoopmanMeanErgodic

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [TopologicalSpace Ω] (F : Flow ℝ Ω) (g : Ω → ℝ)

theorem block_reverse (x : Ω) : block F.reverse g x = block F g (F (-1) x) := by
  have hr : block F.reverse g x = ∫ s in (-1 : ℝ)..0, g (F s x) := by
    simpa only [block, Flow.reverse_apply, zero_sub, sub_zero, neg_zero] using
      intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) (fun s => g (F s x)) (0 : ℝ)
  have hf : block F g (F (-1) x) = ∫ s in (-1 : ℝ)..0, g (F s x) := by
    simp only [block, ← F.map_add]
    simpa only [zero_add, add_neg_cancel] using
      intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1) (fun s => g (F s x)) (-1 : ℝ)
  exact hr.trans hf.symm

variable [MeasurableSpace Ω] [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (hF : ∀ s, MeasurePreserving (F s) μ μ)

theorem blockLp_reverse (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    blockLp F.reverse g μ hg C hbound = operator μ (F (-1)) (hF (-1)) (blockLp F g μ hg C hbound) := by
  apply Lp.ext
  have hrev := blockLp_ae F.reverse g μ hg C hbound
  have hop := Lp.coeFn_compMeasurePreserving (blockLp F g μ hg C hbound) (hF (-1))
  have hforward := (hF (-1)).quasiMeasurePreserving.ae_eq_comp (blockLp_ae F g μ hg C hbound)
  filter_upwards [hrev, hop, hforward] with x hxRev hxOp hxForward
  change blockLp F.reverse g μ hg C hbound x = Lp.compMeasurePreserving (F (-1)) (hF (-1)) (blockLp F g μ hg C hbound) x
  rw [hxRev, hxOp, hxForward, block_reverse]
  rfl

theorem mean_reverse (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    FlowContinuousProfiles.mean F.reverse μ (fun s => hF (-s)) g hg C hbound =
      FlowContinuousProfiles.mean F μ hF g hg C hbound := by
  change limit μ (F (-1)) (hF (-1)) (blockLp F.reverse g μ hg C hbound) =
    limit μ (F 1) (hF 1) (blockLp F g μ hg C hbound)
  rw [blockLp_reverse F g μ hF hg C hbound, KoopmanMeanShift.mean_operator]
  have hfr : ∀ x, F 1 (F (-1) x) = x := fun x => by rw [← F.map_add, add_neg_cancel, Flow.map_zero_apply]
  have hrf : ∀ x, F (-1) (F 1 x) = x := fun x => by rw [← F.map_add, neg_add_cancel, Flow.map_zero_apply]
  exact (KoopmanInverseMeans.mean_eq μ (F 1) (F (-1)) (hF 1) (hF (-1)) hfr hrf (blockLp F g μ hg C hbound)).symm

end VeechDichotomy.FlowReverseMeans
