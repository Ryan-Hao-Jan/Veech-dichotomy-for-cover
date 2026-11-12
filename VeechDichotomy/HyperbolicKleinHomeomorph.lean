module

public import VeechDichotomy.HyperbolicKleinMap

/-! The explicit Klein coordinate map is a genuine global homeomorphism
from the actual upper half-plane to the actual open unit disk. The
inverse uses a positive square root, and both literal inverse formulas
and their actual continuities are proved. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicKleinHomeomorph

open HyperbolicKleinMap Set Topology
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def gap (u : Disk) : ℝ := 1 - Complex.normSq u.val
def inverseDenominator (u : Disk) : ℝ := 1 - u.val.im

theorem gap_pos (u : Disk) : 0 < gap u := by
  change 0 < 1 - Complex.normSq u.val
  rw [Complex.normSq_eq_norm_sq]
  exact BeltramiPlane.denominator_pos u

theorem inverseDenominator_pos (u : Disk) : 0 < inverseDenominator u := by
  have h := gap_pos u
  dsimp only [gap, inverseDenominator] at h ⊢
  rw [Complex.normSq_apply] at h
  nlinarith [sq_nonneg u.val.re, sq_nonneg (u.val.im - 1)]

def inverse (u : Disk) : ℍ :=
  ⟨⟨u.val.re / inverseDenominator u, Real.sqrt (gap u) / inverseDenominator u⟩,
    div_pos (Real.sqrt_pos.mpr (gap_pos u)) (inverseDenominator_pos u)⟩

theorem inverse_normSq (u : Disk) :
    Complex.normSq (inverse u : ℂ) = (1 + u.val.im) / inverseDenominator u := by
  have hs : Real.sqrt (gap u) ^ 2 = gap u := Real.sq_sqrt (gap_pos u).le
  have hnum : u.val.re ^ 2 + Real.sqrt (gap u) ^ 2 = 1 - u.val.im ^ 2 := by
    rw [hs]
    dsimp only [gap]
    simp only [Complex.normSq_apply]
    ring
  have hcalc : (u.val.re / inverseDenominator u) ^ 2 +
      (Real.sqrt (gap u) / inverseDenominator u) ^ 2 = (1 + u.val.im) / inverseDenominator u := by
    rw [div_pow, div_pow, ← add_div, hnum]
    field_simp [(inverseDenominator_pos u).ne']
    dsimp only [inverseDenominator]
    ring
  simpa only [inverse, Complex.normSq_apply, pow_two] using! hcalc

theorem denominator_inverse (u : Disk) : denominator (inverse u) = 2 / inverseDenominator u := by
  rw [denominator, inverse_normSq]
  field_simp [(inverseDenominator_pos u).ne']
  dsimp only [inverseDenominator]
  ring

theorem forward_inverse (u : Disk) : forward (inverse u) = u := by
  apply Subtype.ext
  apply Complex.ext
  · change 2 * (inverse u).re / denominator (inverse u) = u.val.re
    rw [denominator_inverse]
    change 2 * (u.val.re / inverseDenominator u) / (2 / inverseDenominator u) = u.val.re
    field_simp [(inverseDenominator_pos u).ne']
  · change (denominator (inverse u) - 2) / denominator (inverse u) = u.val.im
    rw [denominator_inverse]
    field_simp [(inverseDenominator_pos u).ne']
    dsimp only [inverseDenominator]
    ring

theorem inverse_forward (z : ℍ) : inverse (forward z) = z := by
  have hsub : inverseDenominator (forward z) = 2 / denominator z := one_sub_im z
  have hgap : gap (forward z) = 4 * z.im ^ 2 / denominator z ^ 2 := deficit z
  have hsqrt : Real.sqrt (gap (forward z)) = 2 * z.im / denominator z := by
    rw [hgap, show 4 * z.im ^ 2 / denominator z ^ 2 = (2 * z.im / denominator z) ^ 2 by ring]
    exact Real.sqrt_sq (div_pos (mul_pos (by norm_num) z.im_pos) (denominator_pos z)).le
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (point z).re / inverseDenominator (forward z) = z.re
    rw [hsub]
    change (2 * z.re / denominator z) / (2 / denominator z) = z.re
    field_simp [(denominator_pos z).ne']
  · change Real.sqrt (gap (forward z)) / inverseDenominator (forward z) = z.im
    rw [hsqrt, hsub]
    field_simp [(denominator_pos z).ne']

theorem continuous_inverse : Continuous inverse := by
  have hc : Continuous (fun u : Disk => u.val) := continuous_subtype_val
  have hr := Complex.continuous_re.comp hc
  have hi := Complex.continuous_im.comp hc
  have hd : Continuous inverseDenominator := continuous_const.sub hi
  have hg : Continuous gap := continuous_const.sub (Complex.continuous_normSq.comp hc)
  have hR : Continuous (fun u : Disk => u.val.re / inverseDenominator u) :=
    hr.div hd (fun u => (inverseDenominator_pos u).ne')
  have hI : Continuous (fun u : Disk => Real.sqrt (gap u) / inverseDenominator u) :=
    (Real.continuous_sqrt.comp hg).div hd (fun u => (inverseDenominator_pos u).ne')
  apply continuous_induced_rng.mpr
  change Continuous (fun u : Disk => (inverse u : ℂ))
  have heq : (fun u : Disk => (inverse u : ℂ)) = fun u =>
      ((u.val.re / inverseDenominator u : ℝ) : ℂ) +
        ((Real.sqrt (gap u) / inverseDenominator u : ℝ) : ℂ) * Complex.I := by
    funext u
    apply Complex.ext <;> simp [inverse]
  rw [heq]
  exact (Complex.continuous_ofReal.comp hR).add ((Complex.continuous_ofReal.comp hI).mul continuous_const)

def homeomorph : ℍ ≃ₜ Disk where
  toFun := forward
  invFun := inverse
  left_inv := inverse_forward
  right_inv := forward_inverse
  continuous_toFun := continuous_forward
  continuous_invFun := continuous_inverse

end VeechDichotomy.HyperbolicKleinHomeomorph
