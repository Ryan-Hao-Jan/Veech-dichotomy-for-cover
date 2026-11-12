module

public import VeechDichotomy.NativeDirichletCycleAngles

/-! Every actual congruence cycle through a true Dirichlet corner
has total deficit at least pi/3. The proved effective angle identity
and genuine positive corner deficit force the integer product k*m>2;
the elementary integer cases give the uniform lower bound. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCycleDeficit

open LinearGroup HyperbolicRegularCenters HyperbolicDirichletRegions HyperbolicDirichletCorners
open HyperbolicDirichletInterior DirichletCornerAngles EffectiveCycleSums EffectivePointStabilizers
open scoped UpperHalfPlane

theorem integer_deficit_lower_bound (k m : ℕ) (hm : 0 < m) (hkm : 2 < k * m) :
    Real.pi / 3 ≤ (k : ℝ) * Real.pi - 2 * Real.pi / (m : ℝ) := by
  by_cases h₁ : m = 1
  · subst m
    have hk : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have hp := mul_le_mul_of_nonneg_right hk Real.pi_pos.le
    norm_num only [Nat.cast_one, div_one]
    linarith [Real.pi_pos]
  by_cases h₂ : m = 2
  · subst m
    have hk : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have hp := mul_le_mul_of_nonneg_right hk Real.pi_pos.le
    norm_num only [Nat.cast_ofNat]
    linarith [Real.pi_pos]
  · have hm₃ : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
    have hkNat : 1 ≤ k := by
      by_contra hn
      have hkzero : k = 0 := by omega
      rw [hkzero, zero_mul] at hkm
      omega
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast hkNat
    have hp := mul_le_mul_of_nonneg_right hk Real.pi_pos.le
    have hdiv : 2 * Real.pi / (m : ℝ) ≤ 2 * Real.pi / 3 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hm₃
    linarith

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem cycle_deficit_formula (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (hz : z ∈ frontier (region Γ p)) :
    (∑ w : cycle Γ p z, deficit Γ p w.val) =
      (Fintype.card (cycle Γ p z) : ℝ) * Real.pi - 2 * Real.pi / (effectiveOrder Γ z : ℝ) := by
  simp only [deficit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [NativeDirichletCycleAngles.cycle_width_sum Γ p hp z hz]

theorem cycle_deficit_pos (p : ℍ) (z : ℍ) (hz : z ∈ corners Γ p) :
    0 < ∑ w : cycle Γ p z, deficit Γ p w.val := by
  let w : cycle Γ p z := ⟨z, hz.1, 1, one_smul Γ z⟩
  have hle : deficit Γ p z ≤ ∑ x : cycle Γ p z, deficit Γ p x.val :=
    Finset.single_le_sum (fun x _ => deficit_nonneg Γ p x.val) (Finset.mem_univ w)
  exact (DirichletCornerWidth.deficit_pos Γ p z hz).trans_le hle

theorem cycle_integer_product_gt_two (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (hz : z ∈ corners Γ p) :
    2 < Fintype.card (cycle Γ p z) * effectiveOrder Γ z := by
  have hpos := cycle_deficit_pos Γ p z hz
  rw [cycle_deficit_formula Γ p hp z (corners_subset_frontier Γ p hz)] at hpos
  have hm : (0 : ℝ) < effectiveOrder Γ z := by exact_mod_cast effectiveOrder_pos Γ z
  have hdiv : 2 * Real.pi / (effectiveOrder Γ z : ℝ) < (Fintype.card (cycle Γ p z) : ℝ) * Real.pi := by linarith
  have hmul := (div_lt_iff₀ hm).mp hdiv
  have he : ((Fintype.card (cycle Γ p z) * effectiveOrder Γ z : ℕ) : ℝ) * Real.pi =
      (Fintype.card (cycle Γ p z) : ℝ) * Real.pi * (effectiveOrder Γ z : ℝ) := by rw [Nat.cast_mul]; ring
  rw [← he] at hmul
  have hreal := (mul_lt_mul_iff_of_pos_right Real.pi_pos).mp hmul
  exact_mod_cast hreal

theorem cycle_deficit_ge_pi_div_three (p : ℍ) (hp : RegularCenter Γ p) (z : ℍ) (hz : z ∈ corners Γ p) :
    Real.pi / 3 ≤ ∑ w : cycle Γ p z, deficit Γ p w.val := by
  rw [cycle_deficit_formula Γ p hp z (corners_subset_frontier Γ p hz)]
  exact integer_deficit_lower_bound _ _ (effectiveOrder_pos Γ z) (cycle_integer_product_gt_two Γ p hp z hz)

end VeechDichotomy.NativeCycleDeficit
