module

public import VeechDichotomy.CuspHoroballSeparation

/-! A mixed-height denominator bound separates genuine horoballs
normalized by their reference heights. Only the source endpoint's
translation period controls the required common normalized depth. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelativeHoroballSeparation

open LinearGroup IdealInfinityStabilizers
open scoped UpperHalfPlane

theorem overlap_lower_left_zero (B : SL2) (p : ℍ) (τ Q R : ℝ) (hτ : 0 < τ) (hQ : 0 < Q) (hR : 0 < R)
    (hheight : ∀ n : ℤ, ((B * upper ((n : ℝ) * τ)) • p).im ≤ Q)
    (hdepth : τ ^ 2 + p.im ^ 2 ≤ R ^ 2 * p.im ^ 2) (z : ℍ)
    (hz : R * p.im < z.im) (hg : R * Q < (B • z).im) : B 1 0 = 0 := by
  by_contra hc
  have hl := CuspDenominatorBounds.mixed_lower_left_bound B p τ Q hτ hQ hheight hc
  have hscaled : p.im ≤ Q * (B 1 0 ^ 2 * (R ^ 2 * p.im ^ 2)) :=
    hl.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdepth (sq_nonneg _)) hQ.le)
  have hnorm : 1 ≤ B 1 0 ^ 2 * (R ^ 2 * p.im * Q) := by
    apply (mul_le_mul_iff_of_pos_left p.im_pos).mp
    convert hscaled using 1 <;> ring
  have hp : R ^ 2 * p.im * Q < z.im * (B • z).im := by
    calc
      _ = (R * p.im) * (R * Q) := by ring
      _ ≤ z.im * (R * Q) := mul_le_mul_of_nonneg_right hz.le (mul_pos hR hQ).le
      _ < z.im * (B • z).im := mul_lt_mul_of_pos_left hg z.im_pos
  have hlt : 1 < B 1 0 ^ 2 * (z.im * (B • z).im) :=
    hnorm.trans_lt (mul_lt_mul_of_pos_left hp (sq_pos_of_ne_zero hc))
  exact not_lt_of_ge (CuspHoroballSeparation.height_product_bound B z) hlt

end VeechDichotomy.RelativeHoroballSeparation
