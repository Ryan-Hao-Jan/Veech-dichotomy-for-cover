module

public import VeechDichotomy.CircularIdealTriangleArea

/-! Actual area subtraction for regions bounded by two real-centered
semicircles and a vertical strip. An explicit affine height-square gap
proves containment from just the two endpoint inequalities. The closed
upper arc has actual area zero, so the closed band has precisely the
difference of the two computed ideal-region areas. This does not assume
that arbitrary triangles have already been classified as such bands. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CircularTriangleDifferences

open Set MeasureTheory HyperbolicAffineNormalization CircularIdealTriangleArea
open scoped UpperHalfPlane ENNReal

def gap (c₀ r₀ c₁ r₁ x : ℝ) : ℝ :=
  (r₁ ^ 2 - (x - c₁) ^ 2) - (r₀ ^ 2 - (x - c₀) ^ 2)

theorem gap_difference (c₀ r₀ c₁ r₁ x y : ℝ) :
    gap c₀ r₀ c₁ r₁ x - gap c₀ r₀ c₁ r₁ y = 2 * (c₁ - c₀) * (x - y) := by
  unfold gap
  ring

theorem gap_nonneg_on_interval (c₀ r₀ c₁ r₁ a b : ℝ)
    (ha : 0 ≤ gap c₀ r₀ c₁ r₁ a) (hb : 0 ≤ gap c₀ r₀ c₁ r₁ b)
    {x : ℝ} (hx : x ∈ Icc a b) : 0 ≤ gap c₀ r₀ c₁ r₁ x := by
  by_cases hc : 0 ≤ 2 * (c₁ - c₀)
  · have hprod := mul_nonneg hc (sub_nonneg.mpr hx.1)
    rw [← gap_difference c₀ r₀ c₁ r₁ x a] at hprod
    linarith
  · have hprod := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hc)) (sub_nonneg.mpr hx.2)
    have hg := gap_difference c₀ r₀ c₁ r₁ x b
    nlinarith only [hprod, hg, hb]

theorem upper_region_subset (c₀ r₀ c₁ r₁ a b : ℝ)
    (ha : 0 ≤ gap c₀ r₀ c₁ r₁ a) (hb : 0 ≤ gap c₀ r₀ c₁ r₁ b) :
    circleRegion c₁ r₁ a b ⊆ circleRegion c₀ r₀ a b := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hg := gap_nonneg_on_interval c₀ r₀ c₁ r₁ a b ha hb hz.1
  dsimp only [gap] at hg
  have hn := hz.2
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero] at hn ⊢
  linarith

def closedBand (c₀ r₀ c₁ r₁ a b : ℝ) : Set ℍ :=
  {z | z ∈ circleRegion c₀ r₀ a b ∧ Complex.normSq ((z : ℂ) - (c₁ : ℂ)) ≤ r₁ ^ 2}

theorem circle_null (c r : ℝ) :
    volume {z : ℍ | Complex.normSq ((z : ℂ) - (c : ℂ)) = r ^ 2} = 0 := by
  apply measure_mono_null (t := UpperHalfPlane.coe ⁻¹'
    {w : ℂ | 1 * Complex.normSq w + (-2 * c) * w.re + (c ^ 2 - r ^ 2) = 0}) _
    (HyperbolicBisectorNull.volume_preimage_null
      (ComplexQuadraticNull.quadratic_null 1 (-2 * c) (c ^ 2 - r ^ 2) (Or.inl one_ne_zero)))
  intro z hz
  change Complex.normSq ((z : ℂ) - (c : ℂ)) = r ^ 2 at hz
  change 1 * Complex.normSq (z : ℂ) + (-2 * c) * (z : ℂ).re + (c ^ 2 - r ^ 2) = 0
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero] at hz ⊢
  nlinarith only [hz]

theorem difference_subset_band (c₀ r₀ c₁ r₁ a b : ℝ) :
    circleRegion c₀ r₀ a b \ circleRegion c₁ r₁ a b ⊆ closedBand c₀ r₀ c₁ r₁ a b := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  apply le_of_lt
  apply lt_of_not_ge
  intro hn
  exact hz.2 ⟨hz.1.1, hn⟩

theorem band_difference_null (c₀ r₀ c₁ r₁ a b : ℝ) :
    volume (closedBand c₀ r₀ c₁ r₁ a b \
      (circleRegion c₀ r₀ a b \ circleRegion c₁ r₁ a b)) = 0 := by
  apply measure_mono_null (t := {z : ℍ | Complex.normSq ((z : ℂ) - (c₁ : ℂ)) = r₁ ^ 2}) _
    (circle_null c₁ r₁)
  intro z hz
  have hupper : z ∈ circleRegion c₁ r₁ a b := by
    by_contra hn
    exact hz.2 ⟨hz.1.1, hn⟩
  exact le_antisymm hz.1.2 hupper.2

theorem area_band_eq_difference (c₀ r₀ c₁ r₁ a b : ℝ) :
    volume (closedBand c₀ r₀ c₁ r₁ a b) =
      volume (circleRegion c₀ r₀ a b \ circleRegion c₁ r₁ a b) := by
  exact (measure_eq_measure_of_null_sdiff (difference_subset_band c₀ r₀ c₁ r₁ a b)
    (band_difference_null c₀ r₀ c₁ r₁ a b)).symm

theorem real_area_band (c₀ r₀ c₁ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) {a b : ℝ}
    (ha₀ : c₀ - r₀ < a) (hb₀ : b < c₀ + r₀) (ha₁ : c₁ - r₁ < a) (hb₁ : b < c₁ + r₁)
    (hab : a ≤ b) (hgₐ : 0 ≤ gap c₀ r₀ c₁ r₁ a) (hgᵦ : 0 ≤ gap c₀ r₀ c₁ r₁ b) :
    (volume (closedBand c₀ r₀ c₁ r₁ a b)).toReal =
      areaValue c₀ r₀ a b - areaValue c₁ r₁ a b := by
  have hsub := upper_region_subset c₀ r₀ c₁ r₁ a b hgₐ hgᵦ
  have hfin₀ := (area_lt_top c₀ r₀ hr₀ ha₀ hb₀ hab).ne
  have hfin₁ := (area_lt_top c₁ r₁ hr₁ ha₁ hb₁ hab).ne
  rw [area_band_eq_difference, measure_sdiff hsub (measurableSet_circleRegion c₁ r₁ a b).nullMeasurableSet hfin₁,
    ENNReal.toReal_sub_of_le (measure_mono hsub) hfin₀,
    real_area_formula c₀ r₀ hr₀ ha₀ hb₀ hab, real_area_formula c₁ r₁ hr₁ ha₁ hb₁ hab]

end VeechDichotomy.CircularTriangleDifferences
