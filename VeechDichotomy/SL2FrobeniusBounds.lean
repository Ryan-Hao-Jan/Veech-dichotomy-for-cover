module

public import VeechDichotomy.SL2BottomRowEndpoints

/-! An explicit inverse-matrix Cauchy estimate for genuine SL2
Mobius numerators and denominators. The resulting lower bound is
proved from determinant one and actual complex norm squares. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2FrobeniusBounds

open LinearGroup SL2BottomRowEndpoints HyperbolicKleinMap
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def numerator (B : SL2) (z : ℍ) : ℂ := (B 0 0 : ℂ) * (z : ℂ) + (B 0 1 : ℂ)
def denominatorComplex (B : SL2) (z : ℍ) : ℂ := (B 1 0 : ℂ) * (z : ℂ) + (B 1 1 : ℂ)
def frobeniusSq (B : SL2) : ℝ := B 0 0 ^ 2 + B 0 1 ^ 2 + (B 1 0 ^ 2 + B 1 1 ^ 2)
def totalSq (B : SL2) (z : ℍ) : ℝ := Complex.normSq (numerator B z) + Complex.normSq (denominatorComplex B z)

theorem normSq_combo (r s : ℝ) (u v : ℂ) :
    Complex.normSq ((r : ℂ) * u + (s : ℂ) * v) ≤
      (r ^ 2 + s ^ 2) * (Complex.normSq u + Complex.normSq v) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero]
  nlinarith only [sq_nonneg (r * v.re - s * u.re), sq_nonneg (r * v.im - s * u.im)]

theorem inverse_identities (B : SL2) (z : ℍ) :
    (B 1 1 : ℂ) * numerator B z + (-B 0 1 : ℂ) * denominatorComplex B z = (z : ℂ) ∧
    (-B 1 0 : ℂ) * numerator B z + (B 0 0 : ℂ) * denominatorComplex B z = 1 := by
  have hd := B.property
  rw [Matrix.det_fin_two] at hd
  have hc : (B 0 0 : ℂ) * (B 1 1 : ℂ) - (B 0 1 : ℂ) * (B 1 0 : ℂ) = 1 := by exact_mod_cast hd
  constructor
  · dsimp only [numerator, denominatorComplex]
    linear_combination (z : ℂ) * hc
  · dsimp only [numerator, denominatorComplex]
    linear_combination hc

theorem frobeniusSq_pos (B : SL2) : 0 < frobeniusSq B :=
  add_pos_of_nonneg_of_pos (add_nonneg (sq_nonneg _) (sq_nonneg _)) (rowNormSq_pos B)

theorem denominator_le_total (B : SL2) (z : ℍ) : denominator z ≤ frobeniusSq B * totalSq B z := by
  have hz := normSq_combo (B 1 1) (-B 0 1) (numerator B z) (denominatorComplex B z)
  have ho := normSq_combo (-B 1 0) (B 0 0) (numerator B z) (denominatorComplex B z)
  simp only [Complex.ofReal_neg] at hz ho
  rw [(inverse_identities B z).1] at hz
  rw [(inverse_identities B z).2, Complex.normSq_one] at ho
  simp only [neg_sq] at hz ho
  dsimp only [denominator, frobeniusSq, totalSq]
  nlinarith only [hz, ho]

theorem totalSq_eq (B : SL2) (z : ℍ) :
    totalSq B z = denominatorSq B z * denominator (B • z) := by
  have he : ((B • z : ℍ) : ℂ) = numerator B z / denominatorComplex B z := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    rfl
  have hn : Complex.normSq (denominatorComplex B z) ≠ 0 := (denominatorSq_pos B z).ne'
  unfold denominator
  rw [he, Complex.normSq_div]
  change Complex.normSq (numerator B z) + Complex.normSq (denominatorComplex B z) =
    Complex.normSq (denominatorComplex B z) *
      (Complex.normSq (numerator B z) / Complex.normSq (denominatorComplex B z) + 1)
  field_simp [hn]

theorem denominator_transform_bound (B : SL2) (z : ℍ) :
    denominator z ≤ frobeniusSq B * (denominatorSq B z * denominator (B • z)) := by
  rw [← totalSq_eq]
  exact denominator_le_total B z

end VeechDichotomy.SL2FrobeniusBounds
