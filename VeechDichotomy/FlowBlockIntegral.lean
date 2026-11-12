module

public import VeechDichotomy.FlowUnitBlock

/-! Unit-time smoothing preserves the integral under ACTUAL flow
invariance. Fubini is justified by the proved measurable bounded
integrand on a finite product measure. The Koopman limit of the
smoothed observable therefore retains the original observable's mass. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FlowBlockIntegral

open MeasureTheory Set Filter Topology FlowUnitBlock

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
variable (F : Flow ℝ Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
  (hF : ∀ s, MeasurePreserving (F s) μ μ)

include hF in
theorem integral_block (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    ∫ x, block F g x ∂μ = ∫ x, g x ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hν : ν univ = 1 := by simp [ν]
  let : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.one_lt_top⟩
  have hsm : StronglyMeasurable (fun p : Ω × ℝ => g (F p.2 p.1)) :=
    (hg.comp (F.continuous continuous_snd continuous_fst).measurable).stronglyMeasurable
  have hprod : Integrable (fun p : Ω × ℝ => g (F p.2 p.1)) (μ.prod ν) :=
    Integrable.of_bound hsm.aestronglyMeasurable C (Eventually.of_forall (fun p => hbound (F p.2 p.1)))
  have hinv : ∀ s, ∫ x, g (F s x) ∂μ = ∫ x, g x ∂μ :=
    fun s => (hF s).integral_comp (F.toHomeomorph s).measurableEmbedding g
  calc
    (∫ x, block F g x ∂μ) = ∫ x, ∫ s, g (F s x) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 from zero_le_one)
    _ = ∫ s, ∫ x, g (F s x) ∂μ ∂ν := integral_integral_swap hprod
    _ = ∫ _s, (∫ x, g x ∂μ) ∂ν := by simp_rw [hinv]
    _ = ∫ x, g x ∂μ := by simp only [integral_const, Measure.real, hν, ENNReal.toReal_one, one_smul]

theorem mean_integral (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    ∫ x, KoopmanMeanErgodic.limit μ (F 1) (hF 1) (blockLp F g μ hg C hbound) x ∂μ = ∫ x, g x ∂μ := by
  rw [KoopmanMeanIntegral.integral_limit]
  exact (integral_congr_ae (blockLp_ae F g μ hg C hbound)).trans (integral_block F μ hF g hg C hbound)

end VeechDichotomy.FlowBlockIntegral
