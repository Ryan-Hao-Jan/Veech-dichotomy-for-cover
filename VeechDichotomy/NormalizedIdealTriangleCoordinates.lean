module

public import VeechDichotomy.InverseSquareAreaIntegral
public import VeechDichotomy.ArcsineAreaIntegral
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Actual coordinates and measure formula for a normalized one-ideal
hyperbolic triangle: the region between two vertical lines and above
the unit semicircle. The actual complex image is identified literally,
and the genuine dxdy/y^2 measure becomes the genuine real product
Lebesgue integral. No triangle-area formula is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedIdealTriangleCoordinates

open Set MeasureTheory
open scoped UpperHalfPlane NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

def height (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

def planeRegion (a b : ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ height p.1 ≤ p.2}

def region (a b : ℝ) : Set ℍ := {z | z.re ∈ Icc a b ∧ height z.re ≤ z.im}

theorem native_density_eq (y : ℝ) :
    (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (InverseSquareAreaIntegral.density y) := by
  have hr : (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ) = InverseSquareAreaIntegral.density y := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs,
      InverseSquareAreaIntegral.density]
    simp only [div_pow, sq_abs]
  calc
    (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ)) := by
      rw [ENNReal.ofReal_coe_nnreal]
    _ = _ := congrArg ENNReal.ofReal hr

theorem continuous_height : Continuous height :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))

theorem measurable_planeRegion (a b : ℝ) : MeasurableSet (planeRegion a b) :=
  (measurable_fst measurableSet_Icc).inter
    (isClosed_le (continuous_height.comp continuous_fst) continuous_snd).measurableSet

theorem measurable_region (a b : ℝ) : MeasurableSet (region a b) :=
  (UpperHalfPlane.continuous_re.measurable measurableSet_Icc).inter
    (isClosed_le (continuous_height.comp UpperHalfPlane.continuous_re) UpperHalfPlane.continuous_im).measurableSet

theorem coe_image_region {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    UpperHalfPlane.coe '' region a b = Complex.measurableEquivRealProd ⁻¹' planeRegion a b := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change z.re ∈ Icc a b ∧ height z.re ≤ z.im at hz
    change (z : ℂ).re ∈ Icc a b ∧ height (z : ℂ).re ≤ (z : ℂ).im
    simpa only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hz
  · intro z hz
    change z.re ∈ Icc a b ∧ height z.re ≤ z.im at hz
    have hy : 0 < z.im := (ArcsineAreaIntegral.height_pos ha hb hz.1).trans_le hz.2
    let w : ℍ := ⟨z, hy⟩
    exact ⟨w, hz, rfl⟩

theorem area_eq_plane_integral {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    volume (region a b) = ∫⁻ p : ℝ × ℝ in planeRegion a b,
      ENNReal.ofReal (InverseSquareAreaIntegral.density p.2) := by
  rw [UpperHalfPlane.volume_eq_lintegral, coe_image_region ha hb]
  simp_rw [native_density_eq]
  have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal (InverseSquareAreaIntegral.density p.2))
    (Complex.measurableEquivRealProd ⁻¹' planeRegion a b)
  rw [MeasurableEquiv.image_preimage] at h
  simpa only [Complex.measurableEquivRealProd_apply] using h

end VeechDichotomy.NormalizedIdealTriangleCoordinates
