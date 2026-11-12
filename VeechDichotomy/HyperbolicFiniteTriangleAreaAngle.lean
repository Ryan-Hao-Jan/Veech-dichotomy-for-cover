module

public import VeechDichotomy.HyperbolicTriangleGaussBonnet

/-! The finite-triangle area-angle identity for all three distinct
actual upper-half-plane vertices, including collinear triples. On a
vertical geodesic the extreme angles are zero and the middle angle pi;
actual SL2 invariance and permutation invariance handle every order. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicFiniteTriangleAreaAngle

open LinearGroup Set MeasureTheory HyperbolicDirectionVectors HyperbolicEndpointTangents
open HyperbolicIntrinsicAngles HyperbolicTriangleGaussBonnet HyperbolicTripleNormalization HyperbolicTriangles
open scoped UpperHalfPlane ENNReal

theorem angle_vertical_up (a b c : ℍ) (hab : a.re = b.re) (hac : a.re = c.re)
    (hb : a.im < b.im) (hc : a.im < c.im) : angleAt a b c = 0 := by
  obtain ⟨k, hk, hAB⟩ := vertical_up a b hab hb
  obtain ⟨l, hl, hAC⟩ := vertical_up a c hac hc
  rw [angleAt, hAB, hAC, InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hl, InnerProductGeometry.angle_self Complex.I_ne_zero]

theorem angle_vertical_down (a b c : ℍ) (hab : a.re = b.re) (hac : a.re = c.re)
    (hb : b.im < a.im) (hc : c.im < a.im) : angleAt a b c = 0 := by
  obtain ⟨k, hk, hAB⟩ := vertical_down a b hab hb
  obtain ⟨l, hl, hAC⟩ := vertical_down a c hac hc
  rw [angleAt, hAB, hAC, InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hl,
    InnerProductGeometry.angle_self (neg_ne_zero.mpr Complex.I_ne_zero)]

theorem angle_vertical_opposite (a b c : ℍ) (hab : a.re = b.re) (hac : a.re = c.re)
    (hb : b.im < a.im) (hc : a.im < c.im) : angleAt a b c = Real.pi := by
  obtain ⟨k, hk, hAB⟩ := vertical_down a b hab hb
  obtain ⟨l, hl, hAC⟩ := vertical_up a c hac hc
  rw [angleAt, hAB, hAC, InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hl,
    InnerProductGeometry.angle_neg_self_of_nonzero Complex.I_ne_zero]

theorem ordered_vertical_sum (a b c : ℍ) (hab : a.re = b.re) (hac : a.re = c.re)
    (himab : a.im < b.im) (himbc : b.im < c.im) : angleSum a b c = Real.pi := by
  rw [angleSum, angle_vertical_up a b c hab hac himab (himab.trans himbc),
    angle_vertical_opposite b a c hab.symm (hab.symm.trans hac) himab himbc,
    angle_vertical_down c a b hac.symm (hac.symm.trans hab) (himab.trans himbc) himbc]
  ring

theorem vertical_im_ne {a b : ℍ} (hre : a.re = b.re) (hab : a ≠ b) : a.im ≠ b.im :=
  fun hi => hab (UpperHalfPlane.ext_re_im hre hi)

theorem vertical_angle_sum (a b c : ℍ) (hreab : a.re = b.re) (hreac : a.re = c.re)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : angleSum a b c = Real.pi := by
  have H (u v w : ℍ) (hset : ({a, b, c} : Set ℍ) = {u, v, w})
      (huv : u.re = v.re) (huw : u.re = w.re) (himuv : u.im < v.im) (himvw : v.im < w.im) :
      angleSum a b c = Real.pi :=
    (angleSum_congr_set hab hac hbc hset).trans (ordered_vertical_sum u v w huv huw himuv himvw)
  have himab := vertical_im_ne hreab hab
  have himac := vertical_im_ne hreac hac
  have himbc := vertical_im_ne (hreab.symm.trans hreac) hbc
  rcases lt_or_gt_of_ne himab with hab' | hba'
  · rcases lt_or_gt_of_ne himbc with hbc' | hcb'
    · exact H a b c rfl hreab hreac hab' hbc'
    · rcases lt_or_gt_of_ne himac with hac' | hca'
      · apply H a c b _ hreac hreab hac' hcb'
        ext q
        simp only [mem_insert_iff, mem_singleton_iff]
        tauto
      · apply H c a b _ hreac.symm (hreac.symm.trans hreab) hca' hab'
        ext q
        simp only [mem_insert_iff, mem_singleton_iff]
        tauto
  · rcases lt_or_gt_of_ne himac with hac' | hca'
    · apply H b a c _ hreab.symm (hreab.symm.trans hreac) hba' hac'
      ext q
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    · rcases lt_or_gt_of_ne himbc with hbc' | hcb'
      · apply H b c a _ (hreab.symm.trans hreac) hreab.symm hbc' hca'
        ext q
        simp only [mem_insert_iff, mem_singleton_iff]
        tauto
      · apply H c b a _ (hreac.symm.trans hreab) hreac.symm hcb' hba'
        ext q
        simp only [mem_insert_iff, mem_singleton_iff]
        tauto

theorem collinear_angle_sum {a b c : ℍ} (h : OnCommonGeodesic a b c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : angleSum a b c = Real.pi := by
  obtain ⟨A, d, ha, hb, hc⟩ := h
  rw [← angleSum_smul A]
  exact vertical_angle_sum (A • a) (A • b) (A • c) (ha.trans hb.symm) (ha.trans hc.symm)
    (fun he => hab (MulAction.injective A he)) (fun he => hac (MulAction.injective A he))
    (fun he => hbc (MulAction.injective A he))

theorem real_area_formula (a b c : ℍ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (volume (triangle a b c)).toReal = Real.pi - angleSum a b c := by
  by_cases h : OnCommonGeodesic a b c
  · rw [CollinearHyperbolicTriangles.real_area_zero h, collinear_angle_sum h hab hac hbc, sub_self]
  · exact real_area_noncollinear h

theorem area_formula (a b c : ℍ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    volume (triangle a b c) = ENNReal.ofReal (Real.pi - angleSum a b c) := by
  rw [← real_area_formula a b c hab hac hbc, ENNReal.ofReal_toReal (area_triangle_lt_top a b c).ne]

theorem angle_sum_le_pi (a b c : ℍ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    angleSum a b c ≤ Real.pi := by
  have hn := ENNReal.toReal_nonneg (a := volume (triangle a b c))
  rw [real_area_formula a b c hab hac hbc] at hn
  linarith

end VeechDichotomy.HyperbolicFiniteTriangleAreaAngle
