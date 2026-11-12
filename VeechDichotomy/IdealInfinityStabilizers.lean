module

public import VeechDichotomy.DirichletIdealInfinity

/-! Every genuine group matrix fixing an ideal Dirichlet endpoint at
physical infinity has diagonal entries of square one. Its square is an
actual upper unipotent, with nonzero parameter whenever its off-diagonal
entry is nonzero. This proves the normal form of an existing stabilizer;
existence of a nontrivial stabilizer is not assumed or asserted. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.IdealInfinityStabilizers

open LinearGroup DirichletIdealRadialPoints DirichletIdealInfinity
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def upper (s : ℝ) : SL2 := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem diagonal_product (B : SL2) (hc : B 1 0 = 0) : B 0 0 * B 1 1 = 1 := by
  have h := B.property
  simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using h

theorem height_formula (B : SL2) (p : ℍ) (hc : B 1 0 = 0) : (B • p).im = B 0 0 ^ 2 * p.im := by
  have hd := diagonal_product B hc
  have hdn : B 1 1 ≠ 0 := fun he => by rw [he, mul_zero] at hd; exact zero_ne_one hd
  have hden : Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ B) p) = B 1 1 ^ 2 := by
    change Complex.normSq ((B 1 0 : ℂ) * (p : ℂ) + (B 1 1 : ℂ)) = B 1 1 ^ 2
    rw [hc]
    simp [Complex.normSq_apply, pow_two]
  have hdet : |(Matrix.SpecialLinearGroup.mapGL ℝ B).det.val| = 1 := by
    change |(B : Matrix (Fin 2) (Fin 2) ℝ).det| = 1
    rw [B.property, abs_one]
  have him := UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ B) p
  rw [hdet, one_mul, hden] at him
  change (B • p).im = p.im / B 1 1 ^ 2 at him
  apply (mul_right_cancel₀ (pow_ne_zero 2 hdn))
  rw [him, div_mul_cancel₀ _ (pow_ne_zero 2 hdn)]
  calc
    p.im = (B 0 0 * B 1 1) ^ 2 * p.im := by rw [hd]; ring
    _ = _ := by ring

theorem inverse_entries (B : SL2) : B⁻¹ 0 0 = B 1 1 ∧ B⁻¹ 1 0 = -B 1 0 := by
  constructor <;> simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem diagonal_square (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (γ : Γ) (hc : (γ : SL2) 1 0 = 0) : (γ : SL2) 0 0 ^ 2 = 1 ∧ (γ : SL2) 1 1 = (γ : SL2) 0 0 := by
  let B : SL2 := γ
  have hd := diagonal_product B hc
  have hγ : B 0 0 ^ 2 ≤ 1 := by
    have hh := orbit_height_le Γ p hI γ
    change (B • p).im ≤ p.im at hh
    rw [height_formula B p hc] at hh
    exact (mul_le_mul_iff_of_pos_right p.im_pos).mp (by simpa only [one_mul] using hh)
  have hic : B⁻¹ 1 0 = 0 := by rw [(inverse_entries B).2, hc, neg_zero]
  have hi : B 1 1 ^ 2 ≤ 1 := by
    have hh := orbit_height_le Γ p hI γ⁻¹
    change (B⁻¹ • p).im ≤ p.im at hh
    rw [height_formula B⁻¹ p hic, (inverse_entries B).1] at hh
    exact (mul_le_mul_iff_of_pos_right p.im_pos).mp (by simpa only [one_mul] using hh)
  have hlow : 1 ≤ B 0 0 ^ 2 := by
    calc
      1 = B 0 0 ^ 2 * B 1 1 ^ 2 := by rw [← mul_pow, hd]; norm_num
      _ ≤ B 0 0 ^ 2 * 1 := mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := mul_one _
  have hs : B 0 0 ^ 2 = 1 := le_antisymm hγ hlow
  refine ⟨hs, ?_⟩
  have han : B 0 0 ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  apply mul_left_cancel₀ han
  rw [hd, ← pow_two, hs]

theorem square_normal_form (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (γ : Γ) (hc : (γ : SL2) 1 0 = 0) : (γ : SL2) ^ 2 = upper (2 * (γ : SL2) 0 0 * (γ : SL2) 0 1) := by
  obtain ⟨hs, hd⟩ := diagonal_square Γ p hI γ hc
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, upper, hc, hd]
  · simpa only [pow_two] using hs
  · ring
  · simpa only [pow_two] using hs

theorem exists_nonzero_upper (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (γ : Γ) (hc : (γ : SL2) 1 0 = 0) (hb : (γ : SL2) 0 1 ≠ 0) :
    ∃ s : ℝ, s ≠ 0 ∧ upper s ∈ Γ := by
  have hs := (diagonal_square Γ p hI γ hc).1
  have han : (γ : SL2) 0 0 ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  refine ⟨2 * (γ : SL2) 0 0 * (γ : SL2) 0 1, mul_ne_zero (mul_ne_zero (by norm_num) han) hb, ?_⟩
  rw [← square_normal_form Γ p hI γ hc]
  exact Γ.pow_mem γ.property 2

end VeechDichotomy.IdealInfinityStabilizers
