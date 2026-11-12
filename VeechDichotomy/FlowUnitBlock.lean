module

public import VeechDichotomy.KoopmanMeanIntegral
public import Mathlib.Dynamics.Flow
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The actual unit-time integral of a bounded measurable observable
on a continuous flow is a measurable bounded L2 observable. These are
proved analytic facts, not fields supplied with the flow. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FlowUnitBlock

open MeasureTheory Set Filter Topology

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [TopologicalSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
variable (F : Flow ℝ Ω) (g : Ω → ℝ)

def block (x : Ω) : ℝ := ∫ s in (0 : ℝ)..1, g (F s x)

theorem stronglyMeasurable_block (hg : Measurable g) : StronglyMeasurable (block F g) := by
  have hsm : StronglyMeasurable (fun p : Ω × ℝ => g (F p.2 p.1)) :=
    (hg.comp (F.continuous continuous_snd continuous_fst).measurable).stronglyMeasurable
  have hi : StronglyMeasurable (fun x : Ω => ∫ s in Ioc (0 : ℝ) 1, g (F s x)) := hsm.integral_prod_right'
  change StronglyMeasurable (fun x => ∫ s in (0 : ℝ)..1, g (F s x))
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 from zero_le_one)]
  exact hi

omit [MeasurableSpace Ω] [BorelSpace Ω] in
theorem block_bound (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) (x : Ω) : ‖block F g x‖ ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun s => g (F s x)) (C := C) (fun s _ => hbound (F s x))
  simpa only [block, sub_zero, abs_one, mul_one] using h

theorem time_interval_integrable (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C)
    (x : Ω) (a b : ℝ) : IntervalIntegrable (fun s => g (F s x)) volume a b := by
  have hm : Measurable (fun s : ℝ => g (F s x)) :=
    hg.comp (F.continuous continuous_id continuous_const).measurable
  have hi : IntegrableOn (fun s => g (F s x)) (uIcc a b) volume :=
    IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hm.aestronglyMeasurable C
      (Eventually.of_forall (fun s => hbound (F s x)))
  exact hi.intervalIntegrable

variable (μ : Measure Ω) [IsFiniteMeasure μ]

theorem memLp_block (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) : MemLp (block F g) 2 μ :=
  MemLp.of_bound (stronglyMeasurable_block F g hg).aestronglyMeasurable C
    (Eventually.of_forall (block_bound F g C hbound))

def blockLp (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) : KoopmanMeanErgodic.Space μ :=
  (memLp_block F g μ hg C hbound).toLp (block F g)

theorem blockLp_ae (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    ⇑(blockLp F g μ hg C hbound) =ᵐ[μ] block F g :=
  MemLp.coeFn_toLp (memLp_block F g μ hg C hbound)

end VeechDichotomy.FlowUnitBlock
