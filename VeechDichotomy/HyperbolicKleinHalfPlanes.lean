module

public import VeechDichotomy.HyperbolicKleinHomeomorph
public import Mathlib.Analysis.Normed.Module.Convex

/-! Actual hyperbolic distance half-planes become affine half-planes
in the actual Klein disk. The exact normalization identity preserves
all weak, strict and equality signs. Their Euclidean convexity follows
from actual real linear maps, not a hyperbolic-convexity oracle. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicKleinHalfPlanes

open HyperbolicKleinMap HyperbolicKleinHomeomorph HyperbolicDistanceComparison
open HyperbolicBisectorNull Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def affineForm (p q : ℍ) (u : ℂ) : ℝ :=
  (leading p q + constant p q) / 2 + linear p q / 2 * u.re + (leading p q - constant p q) / 2 * u.im

def linearPart (p q : ℍ) : ℂ →L[ℝ] ℝ :=
  (linear p q / 2) • Complex.reCLM + ((leading p q - constant p q) / 2) • Complex.imCLM

theorem affineForm_eq (p q : ℍ) (u : ℂ) :
    affineForm p q u = (leading p q + constant p q) / 2 + linearPart p q u := by
  simp only [affineForm, linearPart, add_apply, smul_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  ring

theorem normalized_form (p q z : ℍ) : form p q z / denominator z = affineForm p q (point z) := by
  have hd : Complex.normSq (z : ℂ) + 1 ≠ 0 := (denominator_pos z).ne'
  simp only [form, affineForm, point, denominator, UpperHalfPlane.coe_re]
  field_simp [hd]
  ring

theorem dist_le_iff (p q z : ℍ) : dist z p ≤ dist z q ↔ affineForm p q (point z) ≤ 0 := by
  calc
    dist z p ≤ dist z q ↔ form p q z ≤ 0 := HyperbolicDistanceComparison.dist_le_iff p q z
    _ ↔ form p q z / denominator z ≤ 0 := by rw [div_le_iff₀ (denominator_pos z), zero_mul]
    _ ↔ affineForm p q (point z) ≤ 0 := by rw [normalized_form]

theorem dist_lt_iff (p q z : ℍ) : dist z p < dist z q ↔ affineForm p q (point z) < 0 := by
  calc
    dist z p < dist z q ↔ form p q z < 0 := HyperbolicDistanceComparison.dist_lt_iff p q z
    _ ↔ form p q z / denominator z < 0 := by rw [div_lt_iff₀ (denominator_pos z), zero_mul]
    _ ↔ affineForm p q (point z) < 0 := by rw [normalized_form]

theorem dist_eq_iff (p q z : ℍ) : dist z p = dist z q ↔ affineForm p q (point z) = 0 := by
  calc
    dist z p = dist z q ↔ form p q z = 0 := HyperbolicDistanceComparison.dist_eq_iff p q z
    _ ↔ form p q z / denominator z = 0 := by simp [(denominator_pos z).ne']
    _ ↔ affineForm p q (point z) = 0 := by rw [normalized_form]

theorem convex_halfPlane (p q : ℍ) : Convex ℝ {u : ℂ | affineForm p q u ≤ 0} := by
  have heq : {u : ℂ | affineForm p q u ≤ 0} =
      linearPart p q ⁻¹' Iic (-(leading p q + constant p q) / 2) := by
    ext u
    change affineForm p q u ≤ 0 ↔ linearPart p q u ≤ -(leading p q + constant p q) / 2
    rw [affineForm_eq]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact (convex_Iic _).linear_preimage (linearPart p q).toLinearMap

theorem convex_strictHalfPlane (p q : ℍ) : Convex ℝ {u : ℂ | affineForm p q u < 0} := by
  have heq : {u : ℂ | affineForm p q u < 0} =
      linearPart p q ⁻¹' Iio (-(leading p q + constant p q) / 2) := by
    ext u
    change affineForm p q u < 0 ↔ linearPart p q u < -(leading p q + constant p q) / 2
    rw [affineForm_eq]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact (convex_Iio _).linear_preimage (linearPart p q).toLinearMap

theorem image_halfPlane (p q : ℍ) :
    point '' {z : ℍ | dist z p ≤ dist z q} = Metric.ball (0 : ℂ) 1 ∩ {u : ℂ | affineForm p q u ≤ 0} := by
  apply Set.Subset.antisymm
  · rintro u ⟨z, hz, rfl⟩
    exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one z, (dist_le_iff p q z).mp hz⟩
  · intro u hu
    let v : Disk := ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu.1⟩
    let z := inverse v
    have heq : point z = u := congrArg Subtype.val (forward_inverse v)
    refine ⟨z, (dist_le_iff p q z).mpr ?_, heq⟩
    rw [heq]
    exact hu.2

theorem convex_image_halfPlane (p q : ℍ) : Convex ℝ (point '' {z : ℍ | dist z p ≤ dist z q}) := by
  rw [image_halfPlane]
  exact (convex_ball _ _).inter (convex_halfPlane p q)

end VeechDichotomy.HyperbolicKleinHalfPlanes
