module

public import VeechDichotomy.NativeVerticalRayNormalization

/-! Exact lower-unipotent matrices in the native SL2 convention. They
fix the tested vertical velocity and have a nonconstant transverse
vertical shear whenever their actual parameter is nonzero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShearMatrices

open MNEC.LatticeTorus NativeVeech LinearGroup LinearEquivalences NativePrimitiveRectangles

set_option backward.isDefEq.respectTransparency false

def lower (a : ℝ) : SL2 := ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

theorem action (a : ℝ) (p : Plane) : planeEquiv (lower a) p = (p.1, a * p.1 + p.2) := by
  change act (lower a) p = (p.1, a * p.1 + p.2)
  apply Prod.ext <;> simp [act, lower]

theorem linear_action (a : ℝ) (p : Plane) : linear (lower a) p = (p.1, a * p.1 + p.2) := action a p

theorem fixes_vertical (a : ℝ) : planeEquiv (lower a) vertical = vertical := by
  rw [action]
  simp [vertical]

theorem multiply (a b : ℝ) : lower a * lower b = lower (a + b) := by
  apply Subtype.ext
  change (!![1, 0; a, 1] * !![1, 0; b, 1] : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; a + b, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lower_zero : lower 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower]

theorem power (a : ℝ) (n : ℕ) : lower a ^ n = lower ((n : ℝ) * a) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, lower_zero]
  | succ n ih =>
    rw [pow_succ, ih, multiply]
    congr 1
    push_cast
    ring

theorem ne_one {a : ℝ} (ha : a ≠ 0) : lower a ≠ 1 := by
  intro h
  have heq := congrArg (fun A : SL2 => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0) h
  exact ha (by simpa [lower] using heq)

end VeechDichotomy.NativeShearMatrices
