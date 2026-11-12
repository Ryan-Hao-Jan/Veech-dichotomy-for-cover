module

public import VeechDichotomy.SL2ParabolicRayEscape
public import VeechDichotomy.SL2BottomRowEndpoints
public import VeechDichotomy.IdealInfinityStabilizers

/-! A genuine diagonal contracting ray has height tending to zero.
After an actual Mobius transformation whose lower-right entry is
nonzero its height still tends to zero. A positive eventual horoball
height therefore forces that entry to vanish. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DiagonalHyperbolicRayLimits

open LinearGroup Filter Topology NativeTeichmullerRay SL2BottomRowEndpoints
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def point (t : ℝ) : ℍ := diagonal (-t) • UpperHalfPlane.I

theorem point_re (t : ℝ) : (point t).re = 0 := by
  change (((diagonal (-t) • UpperHalfPlane.I : ℍ) : ℂ)).re = 0
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change (((Real.exp (-t) : ℂ) * Complex.I + 0) /
    (0 * Complex.I + (Real.exp (-(-t)) : ℂ))).re = 0
  simp only [zero_mul, zero_add, add_zero, Complex.div_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add, zero_div]

theorem point_im (t : ℝ) : (point t).im = Real.exp (-t) ^ 2 := by
  rw [point, IdealInfinityStabilizers.height_formula (diagonal (-t)) UpperHalfPlane.I (by simp [diagonal])]
  simp [diagonal]

theorem height_tendsto : Tendsto (fun t => (point t).im) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  simpa only [point_im, zero_pow (by norm_num : 2 ≠ 0)] using! he.pow 2

theorem transformed_height_tendsto (C : SL2) (hd : C 1 1 ≠ 0) :
    Tendsto (fun t => (C • point t).im) atTop (𝓝 0) := by
  have hden (t : ℝ) : denominatorSq C (point t) = C 1 0 ^ 2 * (point t).im ^ 2 + C 1 1 ^ 2 := by
    simp only [denominatorSq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, point_re, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    ring
  have hlim : Tendsto (fun t => denominatorSq C (point t)) atTop (𝓝 (C 1 1 ^ 2)) := by
    simpa only [hden, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] using!
      ((height_tendsto.pow 2).const_mul (C 1 0 ^ 2)).add_const (C 1 1 ^ 2)
  simpa only [SL2BottomRowEndpoints.height_formula, zero_div] using!
    height_tendsto.div hlim (pow_ne_zero 2 hd)

theorem lower_right_zero_of_eventual_height (C : SL2) (ε : ℝ) (hε : 0 < ε)
    (hheight : ∀ᶠ t in atTop, ε < (C • point t).im) : C 1 1 = 0 := by
  by_contra hd
  have hlim := transformed_height_tendsto C hd
  have hle : ε ≤ 0 := ge_of_tendsto hlim (hheight.mono (fun _ h => h.le))
  exact not_le_of_gt hε hle

end VeechDichotomy.DiagonalHyperbolicRayLimits
