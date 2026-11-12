module

public import VeechDichotomy.IdealInfinityStabilizers

/-! Opposite actual height comparisons force the precise scale of an
upper triangular Mobius transformation. Horoballs normalized by the
reference points' heights then correspond exactly. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.TriangularHeightComparison

open LinearGroup
open scoped UpperHalfPlane

theorem height_scale_eq (B : SL2) (p q : ℍ) (hc : B 1 0 = 0)
    (hforward : (B • p).im ≤ q.im) (hbackward : (B⁻¹ • q).im ≤ p.im) :
    B 0 0 ^ 2 * p.im = q.im := by
  have he := IdealInfinityStabilizers.height_formula B (B⁻¹ • q) hc
  rw [smul_inv_smul] at he
  have hle : q.im ≤ B 0 0 ^ 2 * p.im := by
    rw [he]
    exact mul_le_mul_of_nonneg_left hbackward (sq_nonneg _)
  rw [IdealInfinityStabilizers.height_formula B p hc] at hforward
  exact le_antisymm hforward hle

theorem normalized_horoball_iff (B : SL2) (p q z : ℍ) (R : ℝ) (hc : B 1 0 = 0)
    (hforward : (B • p).im ≤ q.im) (hbackward : (B⁻¹ • q).im ≤ p.im) :
    R * q.im < (B • z).im ↔ R * p.im < z.im := by
  have he := height_scale_eq B p q hc hforward hbackward
  have han : B 0 0 ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at he
    exact q.im_ne_zero he.symm
  rw [IdealInfinityStabilizers.height_formula B z hc, ← he]
  have hr : R * (B 0 0 ^ 2 * p.im) = B 0 0 ^ 2 * (R * p.im) := by ring
  rw [hr]
  exact mul_lt_mul_iff_of_pos_left (sq_pos_of_ne_zero han)

end VeechDichotomy.TriangularHeightComparison
