module

public import VeechDichotomy.HyperbolicBisectorShapes
public import VeechDichotomy.LinearGroup

/-! Actual vertical lines and real-centered semicircles in the genuine
Poincare metric are ranges of isometric embeddings of the real line.
Vertical logarithmic height gives the first parameterization; an explicit
determinant-one real Mobius map normalizes every positive semicircle to
the vertical axis. Thus actual bisector shapes are intrinsic geodesic lines. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicGeodesicLines

open LinearGroup HyperbolicBisectorShapes HyperbolicBisectorNull Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def verticalPoint (c t : ℝ) : ℍ := ⟨⟨c, Real.exp t⟩, Real.exp_pos t⟩

theorem vertical_isometry (c : ℝ) : Isometry (verticalPoint c) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [UpperHalfPlane.dist_of_re_eq (show (verticalPoint c s).re = (verticalPoint c t).re from rfl)]
  change dist (Real.log (Real.exp s)) (Real.log (Real.exp t)) = dist s t
  rw [Real.log_exp, Real.log_exp]

theorem range_vertical (c : ℝ) : range (verticalPoint c) = vertical c := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    rfl
  · intro hz
    refine ⟨Real.log z.im, ?_⟩
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hz.symm
    · exact Real.exp_log z.im_pos

def normalizer (c r : ℝ) (hr : 0 < r) : SL2 :=
  ⟨!![1, r - c; -1 / (2 * r), (r + c) / (2 * r)], by
    rw [Matrix.det_fin_two]
    change 1 * ((r + c) / (2 * r)) - (r - c) * (-1 / (2 * r)) = 1
    field_simp [hr.ne']
    ring⟩

theorem normalized_re_zero_iff (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (normalizer c r hr • z).re = 0 ↔ z ∈ semicircle c r := by
  let d : ℂ := (((-1 / (2 * r) : ℝ)) : ℂ) * (z : ℂ) + (((r + c) / (2 * r) : ℝ) : ℂ)
  let n : ℝ := (z.re + (r - c)) * ((-1 / (2 * r)) * z.re + (r + c) / (2 * r)) +
    z.im * ((-1 / (2 * r)) * z.im)
  have hd : d ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    change d.im = 0 at hi
    have heq : (-1 / (2 * r)) * z.im = 0 := by
      simpa only [d, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, add_zero] using hi
    exact mul_ne_zero (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hr.ne')) z.im_ne_zero heq
  have hformula : ((normalizer c r hr • z : ℍ) : ℂ) = ((z : ℂ) + ((r - c : ℝ) : ℂ)) / d := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [normalizer, d]
  have hre : (normalizer c r hr • z).re = n / Complex.normSq d := by
    rw [← UpperHalfPlane.coe_re, hformula, Complex.div_re]
    dsimp only [d, n]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      zero_mul, add_zero, sub_zero]
    ring
  have hn : n = (r ^ 2 - Complex.normSq ((z : ℂ) - (c : ℂ))) / (2 * r) := by
    dsimp only [n]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    field_simp [hr.ne']
    ring
  change (normalizer c r hr • z).re = 0 ↔ ‖(z : ℂ) - (c : ℂ)‖ = r
  rw [hre, hn]
  have hdn : Complex.normSq d ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_pos_iff.mpr hd).ne'
  have hrr : 2 * r ≠ 0 := mul_ne_zero (by norm_num) hr.ne'
  simp only [div_eq_zero_iff, hdn, hrr, or_false, sub_eq_zero]
  constructor
  · intro h
    apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    rw [Complex.sq_norm]
    exact h.symm
  · intro h
    rw [← Complex.sq_norm, h]

def circlePoint (c r : ℝ) (hr : 0 < r) (t : ℝ) : ℍ :=
  (normalizer c r hr)⁻¹ • verticalPoint 0 t

theorem circle_isometry (c r : ℝ) (hr : 0 < r) : Isometry (circlePoint c r hr) :=
  (isometry_smul ℍ (normalizer c r hr)⁻¹).comp (vertical_isometry 0)

theorem range_circle (c r : ℝ) (hr : 0 < r) : range (circlePoint c r hr) = semicircle c r := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    apply (normalized_re_zero_iff c r hr _).mp
    change (normalizer c r hr • ((normalizer c r hr)⁻¹ • verticalPoint 0 t)).re = 0
    rw [smul_inv_smul]
    rfl
  · intro hz
    have hvertical : normalizer c r hr • z ∈ vertical 0 := (normalized_re_zero_iff c r hr z).mpr hz
    obtain ⟨t, ht⟩ := (range_vertical 0).symm ▸ hvertical
    refine ⟨t, ?_⟩
    change (normalizer c r hr)⁻¹ • verticalPoint 0 t = z
    rw [ht, inv_smul_smul]

theorem bisector_isometricLine {p q : ℍ} (hpq : p ≠ q) :
    ∃ f : ℝ → ℍ, Isometry f ∧ range f = bisector p q := by
  rcases exists_shape hpq with ⟨c, hc⟩ | ⟨c, r, hr, hc⟩
  · exact ⟨verticalPoint c, vertical_isometry c, (range_vertical c).trans hc.symm⟩
  · exact ⟨circlePoint c r hr, circle_isometry c r hr, (range_circle c r hr).trans hc.symm⟩

end VeechDichotomy.HyperbolicGeodesicLines
