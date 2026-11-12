module

public import VeechDichotomy.UpperUnipotentPowers
public import VeechDichotomy.SL2BottomRowEndpoints
public import Mathlib.Algebra.Order.Floor.Ring

/-! A genuine upper translation period and an actual orbit-height
bound give a uniform lower-left matrix bound. Integer translation
normalizes the bottom row in a bounded interval; the actual Mobius
height formula supplies the estimate, including its mixed-height form. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CuspDenominatorBounds

open LinearGroup IdealInfinityStabilizers SL2BottomRowEndpoints
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem reduce_mod_period (x τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℤ, 0 ≤ x + (n : ℝ) * τ ∧ x + (n : ℝ) * τ < τ := by
  refine ⟨-⌊x / τ⌋, ?_, ?_⟩
  · simpa only [Int.cast_neg, neg_mul, ← sub_eq_add_neg] using Int.sub_floor_div_mul_nonneg x hτ
  · simpa only [Int.cast_neg, neg_mul, ← sub_eq_add_neg] using Int.sub_floor_div_mul_lt x hτ

theorem right_upper_entries (B : SL2) (t : ℝ) :
    (B * upper t) 1 0 = B 1 0 ∧ (B * upper t) 1 1 = B 1 0 * t + B 1 1 := by
  constructor <;> simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, upper]

theorem denominator_right_upper (B : SL2) (p : ℍ) (t : ℝ) (hc : B 1 0 ≠ 0) :
    denominatorSq (B * upper t) p = B 1 0 ^ 2 * ((p.re + B 1 1 / B 1 0 + t) ^ 2 + p.im ^ 2) := by
  unfold denominatorSq
  rw [(right_upper_entries B t).1, (right_upper_entries B t).2]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    zero_mul, add_zero, sub_zero]
  field_simp [hc]
  ring

theorem mixed_lower_left_bound (B : SL2) (p : ℍ) (τ Q : ℝ) (hτ : 0 < τ) (hQ : 0 < Q)
    (hheight : ∀ n : ℤ, ((B * upper ((n : ℝ) * τ)) • p).im ≤ Q) (hc : B 1 0 ≠ 0) :
    p.im ≤ Q * (B 1 0 ^ 2 * (τ ^ 2 + p.im ^ 2)) := by
  obtain ⟨n, hn₀, hn₁⟩ := reduce_mod_period (p.re + B 1 1 / B 1 0) τ hτ
  have hh := hheight n
  rw [SL2BottomRowEndpoints.height_formula] at hh
  have hnum := (div_le_iff₀ (denominatorSq_pos (B * upper ((n : ℝ) * τ)) p)).mp hh
  rw [denominator_right_upper B p _ hc] at hnum
  have hsq : (p.re + B 1 1 / B 1 0 + (n : ℝ) * τ) ^ 2 ≤ τ ^ 2 :=
    (sq_le_sq₀ hn₀ hτ.le).mpr hn₁.le
  have hbound : B 1 0 ^ 2 * ((p.re + B 1 1 / B 1 0 + (n : ℝ) * τ) ^ 2 + p.im ^ 2) ≤
      B 1 0 ^ 2 * (τ ^ 2 + p.im ^ 2) :=
    mul_le_mul_of_nonneg_left (add_le_add hsq le_rfl) (sq_nonneg _)
  exact hnum.trans (mul_le_mul_of_nonneg_left hbound hQ.le)

theorem subgroup_lower_left_bound (Γ : Subgroup SL2) (p : ℍ)
    (hI : Complex.I ∈ DirichletIdealRadialPoints.idealBoundary Γ p)
    (τ : ℝ) (hτ : 0 < τ) (hmem : upper τ ∈ Γ) (γ : Γ) (hc : (γ : SL2) 1 0 ≠ 0) :
    1 ≤ (γ : SL2) 1 0 ^ 2 * (τ ^ 2 + p.im ^ 2) := by
  have hh (n : ℤ) : (((γ : SL2) * upper ((n : ℝ) * τ)) • p).im ≤ p.im := by
    exact DirichletIdealInfinity.orbit_height_le Γ p hI
      ⟨(γ : SL2) * upper ((n : ℝ) * τ), Γ.mul_mem γ.property (UpperUnipotentPowers.integer_multiple_mem Γ τ hmem n)⟩
  have h := mixed_lower_left_bound γ p τ p.im hτ p.im_pos hh hc
  exact (mul_le_mul_iff_of_pos_left p.im_pos).mp (by simpa only [mul_one] using h)

end VeechDichotomy.CuspDenominatorBounds
