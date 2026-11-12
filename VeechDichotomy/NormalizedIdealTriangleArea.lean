module

public import VeechDichotomy.NormalizedIdealTriangleCoordinates

/-! The actual normalized one-ideal hyperbolic triangle has actual
dxdy/y^2 area arcsin(b)-arcsin(a). Genuine product-measure Tonelli reduces
its actual epigraph region to the proved inverse-square vertical integral
and the proved arcsine horizontal integral. No area formula is supplied
as a hypothesis or oracle. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedIdealTriangleArea

open NormalizedIdealTriangleCoordinates Set MeasureTheory
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

theorem measurable_vertical_density : Measurable (fun y : ℝ => ENNReal.ofReal (InverseSquareAreaIntegral.density y)) :=
  ENNReal.measurable_ofReal.comp ((measurable_const.div measurable_id).pow_const 2)

theorem plane_integral_eq_iterated (a b : ℝ) :
    (∫⁻ p : ℝ × ℝ in planeRegion a b, ENNReal.ofReal (InverseSquareAreaIntegral.density p.2)) =
      ∫⁻ x in Icc a b, ∫⁻ y in Ici (height x), ENNReal.ofReal (InverseSquareAreaIntegral.density y) := by
  classical
  let F : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (InverseSquareAreaIntegral.density y)
  let f : ℝ × ℝ → ℝ≥0∞ := (planeRegion a b).indicator (fun p => F p.2)
  have hfm : Measurable f := (measurable_vertical_density.comp measurable_snd).indicator (measurable_planeRegion a b)
  have hpoint (x y : ℝ) : f (x, y) = (Icc a b).indicator (fun x => (Ici (height x)).indicator F y) x := by
    dsimp only [f]
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
      by_cases hy : y ∈ Ici (height x)
      · have hxy : (x, y) ∈ planeRegion a b := ⟨hx, hy⟩
        rw [indicator_of_mem hxy, indicator_of_mem hy]
      · have hxy : (x, y) ∉ planeRegion a b := fun h => hy h.2
        rw [indicator_of_notMem hxy, indicator_of_notMem hy]
    · have hxy : (x, y) ∉ planeRegion a b := fun h => hx h.1
      rw [indicator_of_notMem hxy, indicator_of_notMem hx]
  calc
    (∫⁻ p : ℝ × ℝ in planeRegion a b, F p.2) = ∫⁻ p : ℝ × ℝ, f p :=
      (lintegral_indicator (measurable_planeRegion a b) _).symm
    _ = ∫⁻ x : ℝ, ∫⁻ y : ℝ, f (x, y) := by
      change (∫⁻ p : ℝ × ℝ, f p ∂((volume : Measure ℝ).prod volume)) = _
      exact lintegral_prod f hfm.aemeasurable
    _ = ∫⁻ x : ℝ, (Icc a b).indicator (fun x => ∫⁻ y in Ici (height x), F y) x := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ Icc a b
      · simp only [hpoint, indicator_of_mem hx, lintegral_indicator measurableSet_Ici]
      · simp only [hpoint, indicator_of_notMem hx, lintegral_zero]
    _ = ∫⁻ x in Icc a b, ∫⁻ y in Ici (height x), F y := lintegral_indicator measurableSet_Icc _

theorem area_formula {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    volume (region a b) = ENNReal.ofReal (Real.arcsin b - Real.arcsin a) := by
  rw [area_eq_plane_integral ha hb, plane_integral_eq_iterated]
  calc
    (∫⁻ x in Icc a b, ∫⁻ y in Ici (height x), ENNReal.ofReal (InverseSquareAreaIntegral.density y)) =
        ∫⁻ x in Icc a b, ENNReal.ofReal (1 / height x) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact InverseSquareAreaIntegral.lintegral_density_Ici (ArcsineAreaIntegral.height_pos ha hb hx)
    _ = ENNReal.ofReal (Real.arcsin b - Real.arcsin a) := ArcsineAreaIntegral.lintegral_Icc ha hb hab

theorem area_lt_top {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) : volume (region a b) < ∞ := by
  rw [area_formula ha hb hab]
  exact ENNReal.ofReal_lt_top

end VeechDichotomy.NormalizedIdealTriangleArea
