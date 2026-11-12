module

public import VeechDichotomy.NormalizedIdealTriangleExhaustion
public import VeechDichotomy.HyperbolicBisectorNull

/-! The actual normalized triangle with ideal endpoints -1,1,infinity
has genuine hyperbolic area pi. Monotone exhaustion computes the open
strip; its difference from the closed coordinate region lies on the two
actual null vertical lines. No ideal-triangle area is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedFullIdealTriangleArea

open NormalizedIdealTriangleCoordinates NormalizedIdealTriangleExhaustion Set MeasureTheory
open scoped UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

def fullRegion : Set ℍ := region (-1) 1

def verticalBoundary : Set ℍ :=
  UpperHalfPlane.coe ⁻¹' {z : ℂ | z.re = -1} ∪ UpperHalfPlane.coe ⁻¹' {z : ℂ | z.re = 1}

theorem verticalBoundary_null : volume verticalBoundary = 0 :=
  measure_union_null
    (HyperbolicBisectorNull.volume_preimage_null (ComplexQuadraticNull.vertical_null (-1)))
    (HyperbolicBisectorNull.volume_preimage_null (ComplexQuadraticNull.vertical_null 1))

theorem openRegion_subset_fullRegion : openRegion ⊆ fullRegion := by
  intro z hz
  exact ⟨⟨hz.1.le, hz.2.1.le⟩, hz.2.2⟩

theorem difference_subset_boundary : fullRegion \ openRegion ⊆ verticalBoundary := by
  intro z hz
  by_cases hleft : z.re = -1
  · exact Or.inl (by change (z : ℂ).re = -1; simpa only [UpperHalfPlane.coe_re] using hleft)
  · by_cases hright : z.re = 1
    · exact Or.inr (by change (z : ℂ).re = 1; simpa only [UpperHalfPlane.coe_re] using hright)
    · apply False.elim
      apply hz.2
      exact ⟨lt_of_le_of_ne hz.1.1.1 (fun he => hleft he.symm), lt_of_le_of_ne hz.1.1.2 hright, hz.1.2⟩

theorem fullRegion_area_eq_open : volume fullRegion = volume openRegion := by
  have hn : volume (fullRegion \ openRegion) = 0 :=
    measure_mono_null difference_subset_boundary verticalBoundary_null
  apply le_antisymm _ (measure_mono openRegion_subset_fullRegion)
  calc
    volume fullRegion ≤ volume (openRegion ∪ (fullRegion \ openRegion)) := by
      apply measure_mono
      intro z hz
      by_cases ho : z ∈ openRegion
      · exact Or.inl ho
      · exact Or.inr ⟨hz, ho⟩
    _ ≤ volume openRegion + volume (fullRegion \ openRegion) := measure_union_le _ _
    _ = volume openRegion := by rw [hn, add_zero]

theorem area_full : volume fullRegion = ENNReal.ofReal Real.pi := by
  rw [fullRegion_area_eq_open, openRegion_area]

theorem area_pos : 0 < volume fullRegion := by
  rw [area_full]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

theorem area_lt_top : volume fullRegion < ∞ := by
  rw [area_full]
  exact ENNReal.ofReal_lt_top

end VeechDichotomy.NormalizedFullIdealTriangleArea
