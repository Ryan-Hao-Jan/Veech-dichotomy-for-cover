module

public import VeechDichotomy.SL2FrobeniusBounds

/-! An actual continuous Klein functional vanishes at an actual
bottom-row ideal endpoint. Bounded transformed real and imaginary
coordinates force a uniform positive value, excluding that endpoint
from the actual closure of the given points. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KleinRowSeparation

open LinearGroup Set HyperbolicKleinMap SL2BottomRowEndpoints SL2FrobeniusBounds
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def support (B : SL2) (v : ℂ) : ℝ := B 1 0 ^ 2 + B 1 1 ^ 2 +
  2 * B 1 0 * B 1 1 * v.re + (B 1 0 ^ 2 - B 1 1 ^ 2) * v.im

theorem continuous_support (B : SL2) : Continuous (support B) := by unfold support; fun_prop

theorem support_endpoint (B : SL2) : support B (endpoint B) = 0 := by
  have hn : B 1 0 ^ 2 + B 1 1 ^ 2 ≠ 0 := (rowNormSq_pos B).ne'
  simp only [support, endpoint, ProjectiveRowBoundary.point]
  field_simp [hn]
  ring

theorem support_point (B : SL2) (z : ℍ) : support B (point z) = 2 * denominatorSq B z / denominator z := by
  simp only [support, point, denominatorSq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, add_zero, sub_zero]
  field_simp [(denominator_pos z).ne']
  rw [denominator_formula]
  ring

theorem denominator_bound (w : ℍ) (L Y : ℝ) (hr : |w.re| ≤ L) (hi : w.im ≤ Y) :
    denominator w ≤ L ^ 2 + Y ^ 2 + 1 := by
  have hrs : w.re ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hr)).mpr hr
  have his : w.im ^ 2 ≤ Y ^ 2 := (sq_le_sq₀ w.im_pos.le (w.im_pos.le.trans hi)).mpr hi
  rw [denominator_formula]
  linarith only [hrs, his]

theorem support_lower_bound (B : SL2) (z : ℍ) (L Y : ℝ)
    (hr : |(B • z).re| ≤ L) (hi : (B • z).im ≤ Y) :
    2 ≤ (frobeniusSq B * (L ^ 2 + Y ^ 2 + 1)) * support B (point z) := by
  have hd : denominator z ≤ frobeniusSq B * (denominatorSq B z * (L ^ 2 + Y ^ 2 + 1)) :=
    (denominator_transform_bound B z).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (denominator_bound (B • z) L Y hr hi) (denominatorSq_pos B z).le)
        (frobeniusSq_pos B).le)
  rw [support_point, ← mul_div_assoc]
  apply (le_div_iff₀ (denominator_pos z)).mpr
  convert mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2) using 1; ring

theorem endpoint_not_mem_closure (B : SL2) (S : Set ℍ) (L Y : ℝ)
    (hr : ∀ z ∈ S, |(B • z).re| ≤ L) (hi : ∀ z ∈ S, (B • z).im ≤ Y) :
    endpoint B ∉ closure (point '' S) := by
  have hsub : point '' S ⊆ {v : ℂ | 2 ≤ (frobeniusSq B * (L ^ 2 + Y ^ 2 + 1)) * support B v} := by
    rintro _ ⟨z, hz, rfl⟩
    exact support_lower_bound B z L Y (hr z hz) (hi z hz)
  have hc : IsClosed {v : ℂ | 2 ≤ (frobeniusSq B * (L ^ 2 + Y ^ 2 + 1)) * support B v} :=
    isClosed_le continuous_const (continuous_const.mul (continuous_support B))
  intro he
  have hb := closure_minimal hsub hc he
  change 2 ≤ (frobeniusSq B * (L ^ 2 + Y ^ 2 + 1)) * support B (endpoint B) at hb
  rw [support_endpoint, mul_zero] at hb
  norm_num at hb

end VeechDichotomy.KleinRowSeparation
