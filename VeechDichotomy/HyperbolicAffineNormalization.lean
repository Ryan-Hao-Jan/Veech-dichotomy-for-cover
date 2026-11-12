module

public import VeechDichotomy.IdealTriangleRealArea

/-! The actual determinant-one matrix taking i to c+i*r acts on every
genuine upper-half-plane point by z |-> r*z+c. This identifies the actual
SL2 images of normalized ideal regions with literal regions above arbitrary
positive real-centered semicircles. All action and set equalities are proved. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicAffineNormalization

open LinearGroup Set MeasureTheory
open NormalizedIdealTriangleCoordinates MobiusIdealTriangleArea
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

def matrix (c r : ℝ) (hr : 0 < r) : SL2 := (⟨⟨c, r⟩, hr⟩ : ℍ).toSL2R

theorem action_coe (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (matrix c r hr • z : ℍ) =
      (⟨(r : ℂ) * (z : ℂ) + (c : ℂ), by
        simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          UpperHalfPlane.coe_im, zero_mul, add_zero] using mul_pos hr z.im_pos⟩ : ℍ) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hs : (Real.sqrt r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  have hsq : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hr.le]
  change ((Real.sqrt r : ℂ) * (z : ℂ) + ((c / Real.sqrt r : ℝ) : ℂ)) /
    (0 * (z : ℂ) + ((1 / Real.sqrt r : ℝ) : ℂ)) = (r : ℂ) * (z : ℂ) + (c : ℂ)
  simp only [Complex.ofReal_div, Complex.ofReal_one, zero_mul, zero_add]
  calc
    _ = (Real.sqrt r : ℂ) ^ 2 * (z : ℂ) + (c : ℂ) := by
      field_simp [hs]
    _ = _ := by rw [hsq]

theorem action_complex (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    ((matrix c r hr • z : ℍ) : ℂ) = (r : ℂ) * (z : ℂ) + (c : ℂ) :=
  congrArg UpperHalfPlane.coe (action_coe c r hr z)

theorem action_re (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (matrix c r hr • z).re = r * z.re + c := by
  rw [← UpperHalfPlane.coe_re, action_complex]
  simp

theorem action_im (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (matrix c r hr • z).im = r * z.im := by
  rw [← UpperHalfPlane.coe_im, action_complex]
  simp

def circleRegion (c r a b : ℝ) : Set ℍ :=
  {z | z.re ∈ Icc a b ∧ r ^ 2 ≤ Complex.normSq ((z : ℂ) - (c : ℂ))}

theorem measurableSet_circleRegion (c r a b : ℝ) : MeasurableSet (circleRegion c r a b) :=
  ((UpperHalfPlane.continuous_re).measurable measurableSet_Icc).inter
    (isClosed_le continuous_const
      (Complex.continuous_normSq.comp (UpperHalfPlane.continuous_coe.sub continuous_const))).measurableSet

theorem circle_height_iff (c r : ℝ) (z : ℍ) :
    Real.sqrt (r ^ 2 - (z.re - c) ^ 2) ≤ z.im ↔
      r ^ 2 ≤ Complex.normSq ((z : ℂ) - (c : ℂ)) := by
  rw [Real.sqrt_le_left z.im_pos.le]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero]
  constructor <;> intro h <;> linarith

theorem action_normSq (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    Complex.normSq (((matrix c r hr • z : ℍ) : ℂ) - (c : ℂ)) = r ^ 2 * Complex.normSq (z : ℂ) := by
  rw [action_complex, add_sub_cancel_right, map_mul, Complex.normSq_ofReal]
  ring

theorem action_mem_circleRegion_iff (c r : ℝ) (hr : 0 < r) (a b : ℝ) (z : ℍ) :
    matrix c r hr • z ∈ circleRegion c r (r * a + c) (r * b + c) ↔ z ∈ region a b := by
  have hlo : r * a + c ≤ r * z.re + c ↔ a ≤ z.re := by
    rw [add_le_add_iff_right, mul_le_mul_iff_of_pos_left hr]
  have hhi : r * z.re + c ≤ r * b + c ↔ z.re ≤ b := by
    rw [add_le_add_iff_right, mul_le_mul_iff_of_pos_left hr]
  have hnorm : r ^ 2 ≤ r ^ 2 * Complex.normSq (z : ℂ) ↔
      1 ≤ Complex.normSq (z : ℂ) := by
    simpa only [mul_one] using
      (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hr) :
        r ^ 2 * 1 ≤ r ^ 2 * Complex.normSq (z : ℂ) ↔ 1 ≤ Complex.normSq (z : ℂ))
  have hheight : height z.re ≤ z.im ↔ 1 ≤ Complex.normSq (z : ℂ) := by
    rw [height, Real.sqrt_le_left z.im_pos.le]
    simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    constructor <;> intro h <;> linarith
  change ((matrix c r hr • z).re ∈ Icc _ _) ∧ _ ↔ _
  rw [action_re, action_normSq]
  simp only [mem_Icc, hlo, hhi, hnorm]
  exact and_congr Iff.rfl hheight.symm

theorem image_region (c r : ℝ) (hr : 0 < r) (a b : ℝ) :
    imageRegion (matrix c r hr) a b = circleRegion c r (r * a + c) (r * b + c) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (action_mem_circleRegion_iff c r hr a b z).mpr hz
  · intro z hz
    refine ⟨(matrix c r hr)⁻¹ • z, ?_, smul_inv_smul _ z⟩
    apply (action_mem_circleRegion_iff c r hr a b _).mp
    rwa [smul_inv_smul]

theorem area_circleRegion (c r : ℝ) (hr : 0 < r) {a b : ℝ}
    (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    volume (circleRegion c r (r * a + c) (r * b + c)) =
      ENNReal.ofReal (Real.arcsin b - Real.arcsin a) := by
  rw [← image_region c r hr, area_imageRegion]
  exact NormalizedIdealTriangleArea.area_formula ha hb hab

end VeechDichotomy.HyperbolicAffineNormalization
