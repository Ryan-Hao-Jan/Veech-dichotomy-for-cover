module

public import VeechDichotomy.VaryingOccupationProfiles

/-! Rational native-style occupation profiles control intervals whose
two endpoints move on the reference-time scale, including negative
endpoints. The normalized interval limit is proved by subtracting the
two cumulative limits, with no shifted-generic-point assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ShiftedOccupationProfiles

open MeasureTheory Set Filter Topology OccupationPrimitive FlowIntegerAverages VaryingOccupationProfiles

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
variable (F : Flow ℝ Ω) (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) (hpos : ∀ x, 0 ≤ g x)

include hg hbound hpos

theorem cumulative {I : Type*} {l : Filter I} {R : I → ℝ} (hR : Tendsto R l atTop) (x : Ω) (m : ℝ)
    (hf : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F g ((a.val : ℝ) * R i) x) l (𝓝 m))
    (hb : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F.reverse g ((a.val : ℝ) * R i) x) l (𝓝 m))
    {A : I → ℝ} {a₀ : ℝ} (hA : Tendsto (fun i => A i / R i) l (𝓝 a₀)) :
    Tendsto (fun i => primitive F g (A i) x / R i) l (𝓝 (a₀ * m)) := by
  have hlim := VaryingOccupationProfiles.varying_scaled F g hg C hbound hpos hR x m hf hb hA
  have heq : ∀ᶠ i in l, scaled F g (R i) (A i / R i) x = primitive F g (A i) x / R i := by
    have hRpos : ∀ᶠ i in l, 0 < R i := hR.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hRpos] with i hi
    unfold scaled
    rw [div_mul_cancel₀ _ hi.ne']
  exact Tendsto.congr' heq hlim

theorem interval_average {I : Type*} {l : Filter I} {R : I → ℝ} (hR : Tendsto R l atTop) (x : Ω) (m : ℝ)
    (hf : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F g ((a.val : ℝ) * R i) x) l (𝓝 m))
    (hb : ∀ a : PositiveRational, Tendsto (fun i => timeAverage F.reverse g ((a.val : ℝ) * R i) x) l (𝓝 m))
    {A B : I → ℝ} {a₀ b₀ : ℝ} (hA : Tendsto (fun i => A i / R i) l (𝓝 a₀))
    (hB : Tendsto (fun i => B i / R i) l (𝓝 b₀)) (hab : a₀ < b₀) :
    Tendsto (fun i => (B i - A i)⁻¹ * ∫ s in A i..B i, g (F s x)) l (𝓝 m) := by
  have hPA := cumulative F g hg C hbound hpos hR x m hf hb hA
  have hPB := cumulative F g hg C hbound hpos hR x m hf hb hB
  have hnum : Tendsto (fun i => (primitive F g (B i) x - primitive F g (A i) x) / R i) l (𝓝 (b₀ * m - a₀ * m)) := by
    simpa only [sub_div] using hPB.sub hPA
  have hden : Tendsto (fun i => (B i - A i) / R i) l (𝓝 (b₀ - a₀)) := by
    simpa only [sub_div] using hB.sub hA
  have hquot := hnum.div hden (sub_pos.mpr hab).ne'
  have heq : ∀ᶠ i in l, ((primitive F g (B i) x - primitive F g (A i) x) / R i) / ((B i - A i) / R i) =
      (B i - A i)⁻¹ * ∫ s in A i..B i, g (F s x) := by
    have hRpos : ∀ᶠ i in l, 0 < R i := hR.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hRpos] with i hi
    have hint : primitive F g (B i) x - primitive F g (A i) x = ∫ s in A i..B i, g (F s x) :=
      intervalIntegral.integral_interval_sub_left (FlowUnitBlock.time_interval_integrable F g hg C hbound x 0 (B i))
        (FlowUnitBlock.time_interval_integrable F g hg C hbound x 0 (A i))
    rw [div_div_div_cancel_right₀ hi.ne', hint, div_eq_mul_inv, mul_comm]
  have hfinal : (b₀ * m - a₀ * m) / (b₀ - a₀) = m := by
    field_simp [(sub_pos.mpr hab).ne']
  simpa only [hfinal] using Tendsto.congr' heq hquot

end VeechDichotomy.ShiftedOccupationProfiles
