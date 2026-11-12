module

public import VeechDichotomy.HyperbolicAffineNormalization
public import VeechDichotomy.HyperbolicCommonGeodesic
public import Mathlib.Tactic.Tauto

/-! Actual normalization of a noncollinear hyperbolic triple to a
vertical side with its third point strictly to the right. A genuine
determinant-one inversion changes the horizontal sign when necessary;
the vertical endpoints are ordered by their actual heights. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicTripleNormalization

open LinearGroup Set HyperbolicAffineNormalization HyperbolicGeodesicLines
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def OnCommonGeodesic (a b c : ℍ) : Prop :=
  ∃ (A : SL2) (d : ℝ), (A • a).re = d ∧ (A • b).re = d ∧ (A • c).re = d

theorem pair_axis (a b : ℍ) : ∃ A : SL2, (A • a).re = 0 ∧ (A • b).re = 0 := by
  obtain ⟨A, d, s, t, hs, ht⟩ := HyperbolicCommonGeodesic.exists_clock_coordinates a b
  have hsa : A • a = verticalPoint d s := by rw [← hs, smul_inv_smul]
  have htb : A • b = verticalPoint d t := by rw [← ht, smul_inv_smul]
  refine ⟨matrix (-d) 1 (by norm_num) * A, ?_, ?_⟩
  · rw [mul_smul, action_re, hsa]
    change 1 * d + -d = 0
    ring
  · rw [mul_smul, action_re, htb]
    change 1 * d + -d = 0
    ring

def inversion : SL2 := ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

theorem inversion_complex (z : ℍ) : ((inversion • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [inversion, div_eq_mul_inv]

theorem inversion_re (z : ℍ) : (inversion • z).re = -z.re / Complex.normSq (z : ℂ) := by
  rw [← UpperHalfPlane.coe_re, inversion_complex, Complex.neg_re, Complex.inv_re]
  simp only [UpperHalfPlane.coe_re, neg_div]

theorem normSq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith [sq_nonneg z.re, sq_pos_of_pos z.im_pos]

theorem first_ne_last {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) : a ≠ c := by
  intro he
  obtain ⟨A, ha, hb⟩ := pair_axis a b
  exact h ⟨A, 0, ha, hb, he ▸ ha⟩

theorem axis_positive {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) :
    ∃ A : SL2, (A • a).re = 0 ∧ (A • c).re = 0 ∧ 0 < (A • b).re := by
  obtain ⟨A, ha, hc⟩ := pair_axis a c
  have hb : (A • b).re ≠ 0 := fun he => h ⟨A, 0, ha, he, hc⟩
  by_cases hpos : 0 < (A • b).re
  · exact ⟨A, ha, hc, hpos⟩
  · have hneg : (A • b).re < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hb
    refine ⟨inversion * A, ?_, ?_, ?_⟩
    · rw [mul_smul, inversion_re, ha, neg_zero, zero_div]
    · rw [mul_smul, inversion_re, hc, neg_zero, zero_div]
    · rw [mul_smul, inversion_re]
      exact div_pos (neg_pos.mpr hneg) (normSq_pos _)

theorem exists_vertical_right {a b c : ℍ} (h : ¬OnCommonGeodesic a b c) :
    ∃ (A : SL2) (u v w : ℍ),
      {u, v, w} = (fun z : ℍ => A • z) '' {a, b, c} ∧
        u.re = w.re ∧ u.im < w.im ∧ u.re < v.re := by
  obtain ⟨A, ha, hc, hb⟩ := axis_positive h
  have him : (A • a).im ≠ (A • c).im := by
    intro he
    apply first_ne_last h
    apply MulAction.injective A
    exact UpperHalfPlane.ext_re_im (ha.trans hc.symm) he
  rcases lt_or_gt_of_ne him with hlt | hgt
  · refine ⟨A, A • a, A • b, A • c, ?_, ha.trans hc.symm, hlt, ?_⟩
    · simp only [image_insert_eq, image_singleton]
    · rwa [ha]
  · refine ⟨A, A • c, A • b, A • a, ?_, hc.trans ha.symm, hgt, ?_⟩
    · ext z
      simp only [image_insert_eq, image_singleton, mem_insert_iff, mem_singleton_iff]
      tauto
    · rwa [hc]

end VeechDichotomy.HyperbolicTripleNormalization
