module

public import VeechDichotomy.IdealInfinityStabilizers

/-! Literal multiplication, inverse and integer powers of the actual
upper unipotents, and their genuine translation action on the half-plane. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UpperUnipotentPowers

open LinearGroup IdealInfinityStabilizers
open scoped UpperHalfPlane

theorem multiply (a b : ℝ) : upper a * upper b = upper (a + b) := by
  apply Subtype.ext
  change (!![1, a; 0, 1] * !![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) = !![1, a + b; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upper_zero : upper 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

theorem inverse (a : ℝ) : (upper a)⁻¹ = upper (-a) := by
  have hp : upper a * upper (-a) = 1 := by rw [multiply, add_neg_cancel, upper_zero]
  calc
    (upper a)⁻¹ = (upper a)⁻¹ * (upper a * upper (-a)) := by rw [hp, mul_one]
    _ = upper (-a) := by group

theorem power (a : ℝ) (n : ℕ) : upper a ^ n = upper ((n : ℝ) * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, upper_zero]
  | succ n ih =>
    rw [pow_succ, ih, multiply]
    congr 1
    push_cast
    ring

theorem integer_power (a : ℝ) (n : ℤ) : upper a ^ n = upper ((n : ℝ) * a) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_natCast] using! power a n
  | negSucc n =>
    rw [zpow_negSucc, power, inverse]
    congr 1
    push_cast
    ring

theorem integer_multiple_mem (Γ : Subgroup SL2) (a : ℝ) (ha : upper a ∈ Γ) (n : ℤ) :
    upper ((n : ℝ) * a) ∈ Γ := by
  rw [← integer_power]
  exact Γ.zpow_mem ha n

theorem coe_smul (s : ℝ) (z : ℍ) : ((upper s • z : ℍ) : ℂ) = (z : ℂ) + (s : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [upper]

theorem re_smul (s : ℝ) (z : ℍ) : (upper s • z).re = z.re + s := by
  have h := congrArg Complex.re (coe_smul s z)
  simpa only [UpperHalfPlane.coe_re, Complex.add_re, Complex.ofReal_re] using h

theorem im_smul (s : ℝ) (z : ℍ) : (upper s • z).im = z.im := by
  have h := congrArg Complex.im (coe_smul s z)
  simpa only [UpperHalfPlane.coe_im, Complex.add_im, Complex.ofReal_im, add_zero] using h

end VeechDichotomy.UpperUnipotentPowers
