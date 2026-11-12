module

public import VeechDichotomy.LinearEquivalences
public import VeechDichotomy.TriangularPowerLift
public import Mathlib.Topology.Algebra.GroupWithZero

/-! Homeomorphic lifts of arbitrary SL2 plane maps through z -> z^k.
Factor the real-linear map as a nonzero complex scalar times a positive
triangular map; lift the scalar by a complex root and the triangular part
by the explicit slit-plane construction.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.SL2PowerLift

open MNEC.LatticeTorus MNEC.NativeRegularTranslationAtlas
open LinearGroup LinearEquivalences TriangularPowerLift

def complexAction (A : SL2) (z : ℂ) : ℂ :=
  toPlane.symm (planeEquiv A (toPlane z))

def firstColumn (A : SL2) : ℂ := ⟨A.1 0 0, A.1 1 0⟩
def secondColumn (A : SL2) : ℂ := ⟨A.1 0 1, A.1 1 1⟩

theorem firstColumn_ne_zero (A : SL2) : firstColumn A ≠ 0 := by
  intro h
  have h0 : A.1 0 0 = 0 := congrArg Complex.re h
  have h1 : A.1 1 0 = 0 := congrArg Complex.im h
  have hd := A.property
  simp only [Matrix.det_fin_two, h0, h1, zero_mul, mul_zero, sub_zero] at hd
  exact zero_ne_one hd

theorem second_div_first_im_pos (A : SL2) : 0 < (secondColumn A / firstColumn A).im := by
  have hd := A.property
  rw [Matrix.det_fin_two] at hd
  have hn : (secondColumn A).im * (firstColumn A).re -
      (secondColumn A).re * (firstColumn A).im = 1 := by
    change A.1 1 1 * A.1 0 0 - A.1 0 1 * A.1 1 0 = 1
    nlinarith [hd]
  rw [Complex.div_im, ← sub_div, hn]
  exact div_pos zero_lt_one (Complex.normSq_pos.mpr (firstColumn_ne_zero A))

def triangularFactor (A : SL2) : PositiveTriangular where
  a := 1
  b := (secondColumn A / firstColumn A).re
  d := (secondColumn A / firstColumn A).im
  a_pos := zero_lt_one
  d_pos := second_div_first_im_pos A

theorem complexAction_columns (A : SL2) (z : ℂ) :
    complexAction A z = firstColumn A * (z.re : ℂ) + secondColumn A * (z.im : ℂ) := by
  change (⟨A.1 0 0 * z.re + A.1 0 1 * z.im,
      A.1 1 0 * z.re + A.1 1 1 * z.im⟩ : ℂ) = _
  apply Complex.ext <;> simp [firstColumn, secondColumn]

theorem triangularFactor_formula (A : SL2) (z : ℂ) :
    TriangularPowerLift.map (triangularFactor A) z =
      (z.re : ℂ) + (secondColumn A / firstColumn A) * (z.im : ℂ) := by
  apply Complex.ext <;> simp [TriangularPowerLift.map, triangularFactor]

theorem factorization (A : SL2) (z : ℂ) :
    complexAction A z = firstColumn A * TriangularPowerLift.map (triangularFactor A) z := by
  rw [complexAction_columns, triangularFactor_formula, mul_add, ← mul_assoc]
  have hc : firstColumn A * (secondColumn A / firstColumn A) = secondColumn A := by
    field_simp [firstColumn_ne_zero A]
  rw [hc]

def scalarRoot (A : SL2) (k : ℕ) : ℂ := firstColumn A ^ (k⁻¹ : ℂ)

theorem scalarRoot_pow (A : SL2) (k : ℕ) (hk : 0 < k) : scalarRoot A k ^ k = firstColumn A :=
  Complex.cpow_nat_inv_pow _ hk.ne'

theorem scalarRoot_ne_zero (A : SL2) (k : ℕ) (hk : 0 < k) : scalarRoot A k ≠ 0 := by
  intro h
  have hp := scalarRoot_pow A k hk
  rw [h, zero_pow hk.ne'] at hp
  exact firstColumn_ne_zero A hp.symm

def rootHomeomorph (A : SL2) (k : ℕ) (hk : 0 < k) : ℂ ≃ₜ ℂ :=
  (TriangularPowerLift.rootHomeomorph (triangularFactor A) k hk).trans
    (Homeomorph.mulLeft₀ (scalarRoot A k) (scalarRoot_ne_zero A k hk))

theorem rootHomeomorph_pow (A : SL2) (k : ℕ) (hk : 0 < k) (z : ℂ) :
    rootHomeomorph A k hk z ^ k = complexAction A (z ^ k) := by
  change (scalarRoot A k * rootLift (triangularFactor A) k z) ^ k = _
  rw [mul_pow, scalarRoot_pow A k hk, rootLift_pow _ hk]
  exact (factorization A (z ^ k)).symm

theorem rootHomeomorph_zero (A : SL2) (k : ℕ) (hk : 0 < k) :
    rootHomeomorph A k hk 0 = 0 := by
  change scalarRoot A k * rootLift (triangularFactor A) k 0 = 0
  rw [rootLift_zero, mul_zero]

end VeechDichotomy.SL2PowerLift
