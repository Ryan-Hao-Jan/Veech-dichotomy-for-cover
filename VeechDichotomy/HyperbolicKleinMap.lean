module

public import VeechDichotomy.HyperbolicDistanceComparison
public import VeechDichotomy.BeltramiPlane

/-! Explicit genuine Klein coordinates for the actual upper half-plane.
The image lies in the actual complex open unit disk by an exact positive
deficit formula. All denominators, signs and continuity are proved. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicKleinMap

open Set Topology
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

abbrev Disk := BeltramiPlane.Parameter

def denominator (z : ℍ) : ℝ := Complex.normSq (z : ℂ) + 1

theorem denominator_pos (z : ℍ) : 0 < denominator z :=
  add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) zero_lt_one

theorem denominator_formula (z : ℍ) : denominator z = z.re ^ 2 + z.im ^ 2 + 1 := by
  simp only [denominator, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

def point (z : ℍ) : ℂ := ⟨2 * z.re / denominator z, (denominator z - 2) / denominator z⟩

theorem deficit (z : ℍ) : 1 - Complex.normSq (point z) = 4 * z.im ^ 2 / denominator z ^ 2 := by
  have hd := (denominator_pos z).ne'
  simp only [point, Complex.normSq_apply]
  field_simp [hd]
  rw [denominator_formula]
  ring

theorem one_sub_im (z : ℍ) : 1 - (point z).im = 2 / denominator z := by
  change 1 - (denominator z - 2) / denominator z = _
  field_simp [(denominator_pos z).ne']
  ring

theorem norm_point_lt_one (z : ℍ) : ‖point z‖ < 1 := by
  have hpos : 0 < 1 - Complex.normSq (point z) := by
    rw [deficit]
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero z.im_ne_zero)) (sq_pos_of_pos (denominator_pos z))
  rw [Complex.normSq_eq_norm_sq] at hpos
  nlinarith [norm_nonneg (point z)]

def forward (z : ℍ) : Disk := ⟨point z, norm_point_lt_one z⟩

theorem continuous_denominator : Continuous denominator :=
  (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).add continuous_const

theorem continuous_point : Continuous point := by
  have hr : Continuous (fun z : ℍ => 2 * z.re / denominator z) :=
    (continuous_const.mul UpperHalfPlane.continuous_re).div continuous_denominator (fun z => (denominator_pos z).ne')
  have hi : Continuous (fun z : ℍ => (denominator z - 2) / denominator z) :=
    (continuous_denominator.sub continuous_const).div continuous_denominator (fun z => (denominator_pos z).ne')
  have heq : point = fun z : ℍ => ((2 * z.re / denominator z : ℝ) : ℂ) +
      (((denominator z - 2) / denominator z : ℝ) : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [point]
  rw [heq]
  exact (Complex.continuous_ofReal.comp hr).add ((Complex.continuous_ofReal.comp hi).mul continuous_const)

theorem continuous_forward : Continuous forward := continuous_point.subtype_mk _

end VeechDichotomy.HyperbolicKleinMap
