module

public import VeechDichotomy.FlowUnitBlock

/-! Averaging the actual unit-block observable at integer flow steps
equals the ACTUAL continuous-time integral average over that integer
interval. The integral identity follows from the flow law, translation
of interval integrals and proved adjacent-interval additivity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FlowIntegerAverages

open MeasureTheory Set Filter Topology Finset FlowUnitBlock

variable {Ω : Type*} [TopologicalSpace Ω]
variable (F : Flow ℝ Ω) (g : Ω → ℝ)

def timeAverage (T : ℝ) (x : Ω) : ℝ := T⁻¹ * ∫ s in (0 : ℝ)..T, g (F s x)

theorem iterate_one (n : ℕ) (x : Ω) : (F 1)^[n] x = F (n : ℝ) x := by
  induction n generalizing x with
  | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, Flow.map_zero_apply]
  | succ n ih =>
    calc
      (F 1)^[n + 1] x = F (n : ℝ) (F 1 x) := by rw [Function.iterate_succ_apply, ih]
      _ = F ((n : ℝ) + 1) x := (F.map_add _ _ _).symm
      _ = F (n + 1 : ℕ) x := by simp only [Nat.cast_succ]

theorem block_iterate (k : ℕ) (x : Ω) :
    block F g ((F 1)^[k] x) = ∫ s in (k : ℝ)..(k : ℝ) + 1, g (F s x) := by
  simp only [block, iterate_one, ← F.map_add]
  simpa only [zero_add, add_comm (1 : ℝ)] using
    intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1) (fun s => g (F s x)) (k : ℝ)

variable [MeasurableSpace Ω] [BorelSpace Ω]

theorem integer_average (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) (n : ℕ) (x : Ω) :
    birkhoffAverage ℝ (F 1) (block F g) n x = timeAverage F g (n : ℝ) x := by
  unfold birkhoffAverage birkhoffSum timeAverage
  change (n : ℝ)⁻¹ * (∑ k ∈ range n, block F g ((F 1)^[k] x)) = _
  congr 1
  calc
    (∑ k ∈ range n, block F g ((F 1)^[k] x)) =
        ∑ k ∈ range n, ∫ s in (k : ℝ)..((k + 1 : ℕ) : ℝ), g (F s x) := by
      apply sum_congr rfl
      intro k _
      rw [block_iterate, Nat.cast_succ]
    _ = ∫ s in (0 : ℝ)..(n : ℝ), g (F s x) := by
      simpa only [Nat.cast_zero] using intervalIntegral.sum_integral_adjacent_intervals
        (a := fun k : ℕ => (k : ℝ)) (n := n)
        (fun k _ => time_interval_integrable F g hg C hbound x _ _)

theorem block_pointwise_averages_ae (μ : Measure Ω) [IsFiniteMeasure μ]
    (hF : MeasurePreserving (F 1) μ μ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    ∀ᵐ x ∂μ, ∀ n : ℕ,
      birkhoffAverage ℝ (F 1) (blockLp F g μ hg C hbound : Ω → ℝ) n x = timeAverage F g (n : ℝ) x := by
  have hrep : ∀ᵐ x ∂μ, ∀ k : ℕ,
      blockLp F g μ hg C hbound ((F 1)^[k] x) = block F g ((F 1)^[k] x) :=
    ae_all_iff.mpr (fun k => (hF.iterate k).quasiMeasurePreserving.ae_eq_comp (blockLp_ae F g μ hg C hbound))
  filter_upwards [hrep] with x hx
  intro n
  rw [← integer_average F g hg C hbound n x]
  unfold birkhoffAverage birkhoffSum
  change (n : ℝ)⁻¹ * (∑ k ∈ range n, blockLp F g μ hg C hbound ((F 1)^[k] x)) = _
  congr 1
  exact sum_congr rfl (fun k _ => hx k)

end VeechDichotomy.FlowIntegerAverages
