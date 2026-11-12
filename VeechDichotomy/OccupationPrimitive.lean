module

public import VeechDichotomy.FlowIntegerAverages
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! Actual cumulative occupation integrals and their scaled versions.
Nonnegative observables give monotone primitives. Forward/backward
averages are identified exactly with positive/negative primitive values. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.OccupationPrimitive

open MeasureTheory Set Filter Topology FlowUnitBlock FlowIntegerAverages

variable {Ω : Type*} [TopologicalSpace Ω] (F : Flow ℝ Ω) (g : Ω → ℝ)

def primitive (T : ℝ) (x : Ω) : ℝ := ∫ s in (0 : ℝ)..T, g (F s x)
def scaled (R a : ℝ) (x : Ω) : ℝ := primitive F g (a * R) x / R

theorem timeAverage_eq (T : ℝ) (x : Ω) : timeAverage F g T x = primitive F g T x / T := by
  simp only [timeAverage, primitive, div_eq_mul_inv, mul_comm]

theorem primitive_zero (x : Ω) : primitive F g 0 x = 0 := by simp [primitive]
theorem scaled_zero (R : ℝ) (x : Ω) : scaled F g R 0 x = 0 := by simp [scaled, primitive_zero]

theorem scaled_pos {R a : ℝ} (hR : R ≠ 0) (ha : a ≠ 0) (x : Ω) :
    scaled F g R a x = a * timeAverage F g (a * R) x := by
  rw [timeAverage_eq]
  unfold scaled
  field_simp [hR, ha]

theorem reverse_timeAverage (T : ℝ) (x : Ω) :
    timeAverage F.reverse g T x = -(primitive F g (-T) x) / T := by
  have hrev : (∫ s in (0 : ℝ)..T, g (F.reverse s x)) = ∫ s in -T..0, g (F s x) := by
    simpa only [Flow.reverse_apply, zero_sub, sub_zero, neg_zero] using
      intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := T) (fun s => g (F s x)) (0 : ℝ)
  have hneg : (∫ s in -T..0, g (F s x)) = -(primitive F g (-T) x) := by
    simpa only [primitive] using intervalIntegral.integral_symm (f := fun s => g (F s x)) (0 : ℝ) (-T)
  unfold timeAverage
  rw [hrev, hneg]
  ring

theorem scaled_neg {R a : ℝ} (hR : R ≠ 0) (ha : a ≠ 0) (x : Ω) :
    scaled F g R a x = a * timeAverage F.reverse g ((-a) * R) x := by
  rw [reverse_timeAverage]
  have hneg : -((-a) * R) = a * R := by ring
  rw [hneg]
  unfold scaled
  field_simp [hR, ha]

theorem scaled_ratio {R : ℝ} (hR : R ≠ 0) (T : ℝ) (x : Ω) :
    scaled F g R (T / R) x / (T / R) = timeAverage F g T x := by
  unfold scaled
  rw [div_mul_cancel₀ _ hR, div_div_div_cancel_right₀ hR, timeAverage_eq]

variable [MeasurableSpace Ω] [BorelSpace Ω]

theorem monotone_primitive (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C)
    (hpos : ∀ x, 0 ≤ g x) (x : Ω) : Monotone (fun T => primitive F g T x) := by
  intro a b hab
  apply sub_nonneg.mp
  change 0 ≤ (∫ s in (0 : ℝ)..b, g (F s x)) - ∫ s in (0 : ℝ)..a, g (F s x)
  rw [intervalIntegral.integral_interval_sub_left (time_interval_integrable F g hg C hbound x 0 b)
    (time_interval_integrable F g hg C hbound x 0 a)]
  exact intervalIntegral.integral_nonneg_of_forall hab (fun s => hpos (F s x))

theorem monotone_scaled (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C)
    (hpos : ∀ x, 0 ≤ g x) {R : ℝ} (hR : 0 < R) (x : Ω) : Monotone (fun a => scaled F g R a x) := by
  intro a b hab
  exact div_le_div_of_nonneg_right
    (monotone_primitive F g hg C hbound hpos x (mul_le_mul_of_nonneg_right hab hR.le)) hR.le

end VeechDichotomy.OccupationPrimitive
