module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Actual nonzero vertical fibers of a positive complex power are
finite, nonempty, and can be chosen with every root in any given disk.
The root bound controls the entire fiber, not just a selected branch. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexSmallPowerFibers

open Set

theorem finite_fiber {k : ℕ} (hk : 0 < k) (w : ℂ) : {z : ℂ | z ^ k = w}.Finite := by
  have h := Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hk w)
  simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using h

theorem small_vertical_fiber {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ (∃ z : ℂ, z ^ k = (ε : ℂ) * Complex.I) ∧
      ∀ z : ℂ, z ^ k = (ε : ℂ) * Complex.I → z ∈ Metric.ball (0 : ℂ) r := by
  let ε : ℝ := (r / 2) ^ k
  have hε : 0 < ε := pow_pos (half_pos hr) k
  refine ⟨ε, hε, IsAlgClosed.exists_pow_nat_eq _ hk, ?_⟩
  intro z hz
  have hn : ‖z‖ ^ k = ε := by
    have h := congrArg norm hz
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε, Complex.norm_I, mul_one] at h
    exact h
  have hlt : ‖z‖ ^ k < r ^ k := by
    rw [hn]
    exact pow_lt_pow_left₀ (half_lt_self hr) (half_pos hr).le hk.ne'
  simpa only [Metric.mem_ball, dist_zero_right] using lt_of_pow_lt_pow_left₀ k hr.le hlt

end VeechDichotomy.ComplexSmallPowerFibers
