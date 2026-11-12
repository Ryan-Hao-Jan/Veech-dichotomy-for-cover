module

public import VeechDichotomy.CuspDenominatorBounds
public import VeechDichotomy.NativeIdealInfinityParabolic

/-! Actual high horoballs are precisely invariant at an ideal
Dirichlet endpoint. The actual denominator estimate excludes overlap
with every group element not fixing infinity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CuspHoroballSeparation

open LinearGroup Set IdealInfinityStabilizers SL2BottomRowEndpoints DirichletIdealRadialPoints
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def horoball (Y : ℝ) : Set ℍ := {z | Y < z.im}
def threshold (p : ℍ) (τ : ℝ) : ℝ := Real.sqrt (τ ^ 2 + p.im ^ 2)

theorem threshold_pos (p : ℍ) (τ : ℝ) : 0 < threshold p τ :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos p.im_pos))

theorem height_product_bound (B : SL2) (z : ℍ) : B 1 0 ^ 2 * (z.im * (B • z).im) ≤ 1 := by
  have hd : B 1 0 ^ 2 * z.im ^ 2 ≤ denominatorSq B z := by
    unfold denominatorSq
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      zero_mul, add_zero, sub_zero]
    nlinarith only [sq_nonneg (B 1 0 * z.re + B 1 1)]
  have he : (B • z).im * denominatorSq B z = z.im :=
    (eq_div_iff (denominatorSq_pos B z).ne').mp (SL2BottomRowEndpoints.height_formula B z)
  have hm := mul_le_mul_of_nonneg_left hd (B • z).im_pos.le
  have hbound : z.im * (B 1 0 ^ 2 * (z.im * (B • z).im)) ≤ z.im * 1 := by
    calc
      _ = (B • z).im * (B 1 0 ^ 2 * z.im ^ 2) := by ring
      _ ≤ (B • z).im * denominatorSq B z := hm
      _ = _ := by rw [he, mul_one]
  exact (mul_le_mul_iff_of_pos_left z.im_pos).mp hbound

theorem high_overlap_lower_left_zero (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (τ : ℝ) (hτ : 0 < τ) (hmem : upper τ ∈ Γ) (γ : Γ) (z : ℍ)
    (hz : z ∈ horoball (threshold p τ)) (hg : γ • z ∈ horoball (threshold p τ)) :
    (γ : SL2) 1 0 = 0 := by
  by_contra hc
  have hlow := CuspDenominatorBounds.subgroup_lower_left_bound Γ p hI τ hτ hmem γ hc
  have hs : threshold p τ ^ 2 = τ ^ 2 + p.im ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hprod : τ ^ 2 + p.im ^ 2 < z.im * (γ • z).im := by
    calc
      _ = threshold p τ * threshold p τ := by rw [← hs]; ring
      _ ≤ z.im * threshold p τ := mul_le_mul_of_nonneg_right hz.le (threshold_pos p τ).le
      _ < z.im * (γ • z).im := mul_lt_mul_of_pos_left hg z.im_pos
  have hlt : 1 < (γ : SL2) 1 0 ^ 2 * (z.im * (γ • z).im) :=
    hlow.trans_lt (mul_lt_mul_of_pos_left hprod (sq_pos_of_ne_zero hc))
  exact not_lt_of_ge (height_product_bound γ z) hlt

theorem nonstabilizer_disjoint (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (τ : ℝ) (hτ : 0 < τ) (hmem : upper τ ∈ Γ) (γ : Γ) (hc : (γ : SL2) 1 0 ≠ 0) :
    Disjoint (horoball (threshold p τ)) ((fun z : ℍ => γ • z) '' horoball (threshold p τ)) := by
  apply Set.disjoint_left.mpr
  rintro _ hg ⟨z, hz, rfl⟩
  exact hc (high_overlap_lower_left_zero Γ p hI τ hτ hmem γ z hz hg)

theorem stabilizer_height_eq (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (γ : Γ) (hc : (γ : SL2) 1 0 = 0) (z : ℍ) : (γ • z).im = z.im := by
  change ((γ : SL2) • z).im = z.im
  rw [IdealInfinityStabilizers.height_formula γ z hc, (diagonal_square Γ p hI γ hc).1, one_mul]

theorem stabilizer_preserves (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (γ : Γ) (hc : (γ : SL2) 1 0 = 0) (Y : ℝ) :
    (fun z : ℍ => γ • z) '' horoball Y = horoball Y := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change Y < (γ • z).im
    rwa [stabilizer_height_eq Γ p hI γ hc]
  · intro z hz
    have hic : ((γ⁻¹ : Γ) : SL2) 1 0 = 0 := by
      change ((γ : SL2)⁻¹) 1 0 = 0
      rw [(inverse_entries γ).2, hc, neg_zero]
    refine ⟨γ⁻¹ • z, ?_, smul_inv_smul γ z⟩
    change Y < (γ⁻¹ • z).im
    rwa [stabilizer_height_eq Γ p hI γ⁻¹ hic]

theorem exists_positive_period (Γ : Subgroup SL2)
    (hex : ∃ s : ℝ, s ≠ 0 ∧ upper s ∈ Γ) : ∃ τ : ℝ, 0 < τ ∧ upper τ ∈ Γ := by
  obtain ⟨s, hs, hmem⟩ := hex
  rcases lt_or_gt_of_ne hs with hn | hp
  · exact ⟨-s, neg_pos.mpr hn, by rw [← UpperUnipotentPowers.inverse]; exact Γ.inv_mem hmem⟩
  · exact ⟨s, hp, hmem⟩

end VeechDichotomy.CuspHoroballSeparation
