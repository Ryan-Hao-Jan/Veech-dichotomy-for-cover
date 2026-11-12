module

public import VeechDichotomy.ProjectiveRowBoundary
public import VeechDichotomy.DirichletIdealInfinity

/-! The actual bottom row of an actual SL2 matrix determines a genuine
ideal endpoint. The exact height and affine-form identities prove that
maximal-height orbit representatives give actual Dirichlet ideal points. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SL2BottomRowEndpoints

open LinearGroup HyperbolicKleinHalfPlanes HyperbolicBisectorNull DirichletIdealRadialPoints
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def rowNormSq (B : SL2) : ℝ := B 1 0 ^ 2 + B 1 1 ^ 2
def denominatorSq (B : SL2) (z : ℍ) : ℝ := Complex.normSq ((B 1 0 : ℂ) * (z : ℂ) + (B 1 1 : ℂ))
def endpoint (B : SL2) : ℂ := ProjectiveRowBoundary.point (B 1 0) (B 1 1)

theorem rowNormSq_pos (B : SL2) : 0 < rowNormSq B := by
  have hne : B 1 0 ≠ 0 ∨ B 1 1 ≠ 0 := by
    by_contra hn
    push Not at hn
    have hd := B.property
    simp only [Matrix.det_fin_two, hn.1, hn.2, mul_zero, sub_self] at hd
    exact zero_ne_one hd
  rcases hne with hc | hd
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hc) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hd)

theorem denominatorSq_pos (B : SL2) (z : ℍ) : 0 < denominatorSq B z :=
  UpperHalfPlane.normSq_denom_pos (Matrix.SpecialLinearGroup.mapGL ℝ B) z.im_ne_zero

theorem norm_endpoint (B : SL2) : ‖endpoint B‖ = 1 :=
  ProjectiveRowBoundary.norm_point _ _ (rowNormSq_pos B)

theorem height_formula (B : SL2) (z : ℍ) : (B • z).im = z.im / denominatorSq B z := by
  have hdet : |(Matrix.SpecialLinearGroup.mapGL ℝ B).det.val| = 1 := by
    change |(B : Matrix (Fin 2) (Fin 2) ℝ).det| = 1
    rw [B.property, abs_one]
  have h := UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ B) z
  rw [hdet, one_mul] at h
  exact h

theorem denominatorSq_eq_one (B : SL2) (p : ℍ) (hh : (B • p).im = p.im) : denominatorSq B p = 1 := by
  rw [height_formula] at hh
  have hm := (div_eq_iff (denominatorSq_pos B p).ne').mp hh
  have he : p.im * 1 = p.im * denominatorSq B p := by simpa only [mul_one] using hm
  exact (mul_left_cancel₀ p.im_ne_zero he).symm

theorem affine_endpoint (B : SL2) (p q : ℍ) : affineForm p q (endpoint B) =
    (q.im * denominatorSq B p - p.im * denominatorSq B q) / rowNormSq B := by
  have hn : B 1 0 ^ 2 + B 1 1 ^ 2 ≠ 0 := (rowNormSq_pos B).ne'
  simp only [affineForm, endpoint, ProjectiveRowBoundary.point, denominatorSq, rowNormSq,
    leading, linear, constant, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    zero_mul, add_zero, sub_zero]
  field_simp [hn]
  ring

theorem endpoint_mem_ideal (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (γ : Γ) (hh : (γ • p).im = p.im) : endpoint γ ∈ idealBoundary Γ p := by
  apply (DirichletClosedHalfPlanes.idealBoundary_iff Γ p (endpoint γ)).mpr
  refine ⟨norm_endpoint γ, ?_⟩
  intro δ
  have hheight := DirichletIdealInfinity.orbit_height_le Γ p hI (γ * δ)
  rw [mul_smul] at hheight
  change ((γ : SL2) • (δ • p)).im ≤ p.im at hheight
  rw [height_formula] at hheight
  have hnum := (div_le_iff₀ (denominatorSq_pos γ (δ • p))).mp hheight
  rw [affine_endpoint, denominatorSq_eq_one γ p hh, mul_one]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hnum) (rowNormSq_pos γ).le

theorem rows_proportional (B C : SL2) (he : endpoint B = endpoint C) :
    B 1 0 * C 1 1 - B 1 1 * C 1 0 = 0 :=
  ProjectiveRowBoundary.proportional_of_point_eq _ _ _ _ (rowNormSq_pos B) (rowNormSq_pos C) he

end VeechDichotomy.SL2BottomRowEndpoints
