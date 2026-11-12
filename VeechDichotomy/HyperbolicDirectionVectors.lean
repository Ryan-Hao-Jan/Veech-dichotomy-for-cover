module

public import VeechDichotomy.HyperbolicTriangleAreaBounds

/-! Explicit endpoint direction vectors in the actual upper half-plane.
Their actual Euclidean norms and inner products are computed from actual
Poincare distances. These identities supply an intrinsic cosine law
without choosing a triangle normalization or assuming tangent covariance. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirectionVectors

open scoped UpperHalfPlane

def verticalCoefficient (a b : ℍ) : ℝ :=
  ((b.re - a.re) ^ 2 + b.im ^ 2 - a.im ^ 2) / (2 * a.im)

def direction (a b : ℍ) : ℂ := ⟨b.re - a.re, verticalCoefficient a b⟩

theorem normSq_formula (a b : ℍ) :
    Complex.normSq (direction a b) = b.im ^ 2 * (Real.cosh (dist a b) ^ 2 - 1) := by
  rw [UpperHalfPlane.cosh_dist']
  simp only [direction, verticalCoefficient, Complex.normSq_apply]
  field_simp [a.im_ne_zero, b.im_ne_zero]
  ring

theorem norm_formula (a b : ℍ) : ‖direction a b‖ = b.im * Real.sinh (dist a b) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg b.im_pos.le (Real.sinh_nonneg_iff.mpr dist_nonneg))).mp
  rw [Complex.sq_norm, normSq_formula, mul_pow, Real.sinh_sq]

theorem direction_eq_zero_iff (a b : ℍ) : direction a b = 0 ↔ a = b := by
  constructor
  · intro hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    change b.re - a.re = 0 at hre
    change verticalCoefficient a b = 0 at him
    have hr := sub_eq_zero.mp hre
    have hn : (b.re - a.re) ^ 2 + b.im ^ 2 - a.im ^ 2 = 0 := by
      exact (div_eq_zero_iff).mp him |>.resolve_right (mul_ne_zero (by norm_num) a.im_ne_zero)
    have hi : a.im = b.im := by nlinarith [a.im_pos, b.im_pos]
    exact UpperHalfPlane.ext_re_im hr.symm hi
  · rintro rfl
    apply Complex.ext <;> simp [direction, verticalCoefficient]

theorem inner_formula (a b c : ℍ) :
    inner ℝ (direction a b) (direction a c) = b.im * c.im *
      (Real.cosh (dist a b) * Real.cosh (dist a c) - Real.cosh (dist b c)) := by
  have hi : inner ℝ (direction a b) (direction a c) =
      (b.re - a.re) * (c.re - a.re) + verticalCoefficient a b * verticalCoefficient a c := by
    simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, direction]
    ring
  rw [hi]
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist']
  dsimp only [verticalCoefficient]
  field_simp [a.im_ne_zero, b.im_ne_zero, c.im_ne_zero]
  ring

end VeechDichotomy.HyperbolicDirectionVectors
