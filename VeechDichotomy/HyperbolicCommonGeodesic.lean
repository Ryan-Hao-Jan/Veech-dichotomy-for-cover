module

public import VeechDichotomy.HyperbolicGeodesicLines

/-! Any two actual upper-half-plane points lie on a genuine complete
isometric geodesic line. Equal real parts give a vertical line; otherwise
the explicitly computed real-centered circle has equal positive radii
to both points. The actual determinant-one normalizer supplies real
isometric clock coordinates for both endpoints. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicCommonGeodesic

open LinearGroup HyperbolicGeodesicLines HyperbolicBisectorShapes Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem exists_clock_coordinates (a b : ℍ) : ∃ (A : SL2) (c s t : ℝ),
    A⁻¹ • verticalPoint c s = a ∧ A⁻¹ • verticalPoint c t = b := by
  by_cases hab : a.re = b.re
  · refine ⟨1, a.re, Real.log a.im, Real.log b.im, ?_, ?_⟩
    · rw [inv_one, one_smul]
      apply UpperHalfPlane.ext
      apply Complex.ext
      · rfl
      · exact Real.exp_log a.im_pos
    · rw [inv_one, one_smul]
      apply UpperHalfPlane.ext
      apply Complex.ext
      · exact hab
      · exact Real.exp_log b.im_pos
  · let c : ℝ := (Complex.normSq (a : ℂ) - Complex.normSq (b : ℂ)) / (2 * (a.re - b.re))
    let r : ℝ := ‖(a : ℂ) - (c : ℂ)‖
    have ha0 : (a : ℂ) - (c : ℂ) ≠ 0 := by
      intro he
      apply a.im_ne_zero
      have hi := congrArg Complex.im he
      simpa using hi
    have hr : 0 < r := norm_pos_iff.mpr ha0
    have hn : Complex.normSq ((a : ℂ) - (c : ℂ)) = Complex.normSq ((b : ℂ) - (c : ℂ)) := by
      dsimp only [c]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      field_simp [sub_ne_zero.mpr hab]
      ring
    have hb : ‖(b : ℂ) - (c : ℂ)‖ = r := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [Complex.sq_norm, Complex.sq_norm]
      exact hn.symm
    let A := normalizer c r hr
    have hA : A • a ∈ vertical 0 := (normalized_re_zero_iff c r hr a).mpr rfl
    have hB : A • b ∈ vertical 0 := (normalized_re_zero_iff c r hr b).mpr hb
    rw [← range_vertical 0] at hA hB
    obtain ⟨s, hs⟩ := hA
    obtain ⟨t, ht⟩ := hB
    refine ⟨A, 0, s, t, ?_, ?_⟩
    · rw [hs, inv_smul_smul]
    · rw [ht, inv_smul_smul]

end VeechDichotomy.HyperbolicCommonGeodesic
