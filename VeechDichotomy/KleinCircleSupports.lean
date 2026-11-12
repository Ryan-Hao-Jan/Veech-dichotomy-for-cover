module

public import VeechDichotomy.CircularTriangleDifferences
public import VeechDichotomy.EuclideanTriangleCoordinates

/-! Literal affine Klein supports for circles passing through a point of
the unit semicircle. The actual circle inequality is divided by the proved
positive Klein denominator, preserving its exact weak and equality signs. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KleinCircleSupports

open HyperbolicKleinMap
open scoped UpperHalfPlane

def support (c b : ℝ) (u : ℂ) : ℝ := (-c) * (u.re - b) + (1 - c * b) * u.im

theorem normalized_circle (c r b : ℝ) (hrad : r ^ 2 = 1 + c ^ 2 - 2 * c * b) (z : ℍ) :
    (Complex.normSq ((z : ℂ) - (c : ℂ)) - r ^ 2) / denominator z = support c b (point z) := by
  have hd := (denominator_pos z).ne'
  simp only [support, point, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero]
  field_simp [hd]
  rw [hrad, denominator_formula]
  ring

theorem circle_le_iff (c r b : ℝ) (hrad : r ^ 2 = 1 + c ^ 2 - 2 * c * b) (z : ℍ) :
    Complex.normSq ((z : ℂ) - (c : ℂ)) ≤ r ^ 2 ↔ support c b (point z) ≤ 0 := by
  rw [← normalized_circle c r b hrad, div_le_iff₀ (denominator_pos z), zero_mul]
  exact sub_nonpos.symm

theorem circle_eq_iff (c r b : ℝ) (hrad : r ^ 2 = 1 + c ^ 2 - 2 * c * b) (z : ℍ) :
    Complex.normSq ((z : ℂ) - (c : ℂ)) = r ^ 2 ↔ support c b (point z) = 0 := by
  rw [← normalized_circle c r b hrad]
  simp only [div_eq_zero_iff, (denominator_pos z).ne', or_false, sub_eq_zero]

end VeechDichotomy.KleinCircleSupports
