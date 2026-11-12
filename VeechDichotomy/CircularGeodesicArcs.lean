module

public import VeechDichotomy.CircularTriangleTangents

/-! Actual semicircle graph arcs are the entire intrinsic metric
segments between their endpoints. Positive affine SL2 normalization,
the exact Klein metric-segment theorem and the literal unit-circle
vertices prove both set inclusions, including the arc's orientation. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CircularGeodesicArcs

open LinearGroup Set HyperbolicMetricSegments HyperbolicKleinGeodesics
open HyperbolicAffineNormalization CircularIdealTriangleArea CircularTriangleTangents
open MobiusIdealTriangleArea
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def graphPoint (c r : ℝ) (hr : 0 < r) (x : ℝ) (hx₀ : c - r < x) (hx₁ : x < c + r) : ℍ :=
  ⟨curve c r x, by simpa [curve] using height_pos hr hx₀ hx₁⟩

theorem graphPoint_re (c r : ℝ) (hr : 0 < r) (x : ℝ) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    (graphPoint c r hr x hx₀ hx₁).re = x := by simp [graphPoint, curve]

theorem affine_vertex (c r : ℝ) (hr : 0 < r) (x : ℝ) (hx₀ : c - r < x) (hx₁ : x < c + r) :
    matrix c r hr • vertex (coord c r x) (coord_left hr hx₀) (coord_right hr hx₁) =
      graphPoint c r hr x hx₀ hx₁ := by
  apply UpperHalfPlane.ext_re_im
  · rw [action_re, graphPoint_re]
    change r * (NormalizedTriangleTangents.curve (coord c r x)).re + c = x
    simpa [NormalizedTriangleTangents.curve] using coord_back c r hr x
  · rw [action_im]
    change r * (NormalizedTriangleTangents.curve (coord c r x)).im = (curve c r x).im
    simpa [NormalizedTriangleTangents.curve, curve] using (height_rescale hr hx₀ hx₁).symm

theorem unit_segment_mem {a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b)
    {x : ℝ} (hx : x ∈ Icc a b) :
    vertex x (ha.trans_le hx.1) (hx.2.trans_lt hb) ∈
      metricSegment (vertex a ha (hab.trans_lt hb)) (vertex b (ha.trans_le hab) hb) := by
  rw [mem_metricSegment_iff, NormalizedIdealKleinTriangle.point_vertex,
    NormalizedIdealKleinTriangle.point_vertex, NormalizedIdealKleinTriangle.point_vertex,
    HorizontalApexTriangles.horizontal_segment hab]
  exact ⟨x, hx, rfl⟩

theorem graphPoint_between (c r : ℝ) (hr : 0 < r) {a b : ℝ}
    (ha : c - r < a) (hb : b < c + r) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Icc a b) :
    graphPoint c r hr x (ha.trans_le hx.1) (hx.2.trans_lt hb) ∈
      metricSegment (graphPoint c r hr a ha (hab.trans_lt hb))
        (graphPoint c r hr b (ha.trans_le hab) hb) := by
  rw [← affine_vertex, ← affine_vertex, ← affine_vertex, smul_mem_metricSegment_iff]
  exact unit_segment_mem (coord_left hr ha) (coord_right hr hb) (coord_mono c hr hab)
    ⟨coord_mono c hr hx.1, coord_mono c hr hx.2⟩

theorem metricSegment_eq_graph (c r : ℝ) (hr : 0 < r) {a b : ℝ}
    (ha : c - r < a) (hb : b < c + r) (hab : a ≤ b) :
    metricSegment (graphPoint c r hr a ha (hab.trans_lt hb))
      (graphPoint c r hr b (ha.trans_le hab) hb) =
        {z : ℍ | ∃ (x : ℝ) (hx : x ∈ Icc a b),
          z = graphPoint c r hr x (ha.trans_le hx.1) (hx.2.trans_lt hb)} := by
  apply Subset.antisymm
  · intro z hz
    rw [← affine_vertex, ← affine_vertex] at hz
    have hnorm : (matrix c r hr)⁻¹ • z ∈
        metricSegment (vertex (coord c r a) (coord_left hr ha) (coord_right hr (hab.trans_lt hb)))
          (vertex (coord c r b) (coord_left hr (ha.trans_le hab)) (coord_right hr hb)) := by
      apply (smul_mem_metricSegment_iff (matrix c r hr) _ _ _).mp
      simpa only [smul_inv_smul] using hz
    rw [mem_metricSegment_iff, NormalizedIdealKleinTriangle.point_vertex,
      NormalizedIdealKleinTriangle.point_vertex,
      HorizontalApexTriangles.horizontal_segment (coord_mono c hr hab)] at hnorm
    obtain ⟨t, ht, hpoint⟩ := hnorm
    let w := vertex t ((coord_left hr ha).trans_le ht.1) (ht.2.trans_lt (coord_right hr hb))
    have hw : w = (matrix c r hr)⁻¹ • z := by
      apply HyperbolicGeodesicHulls.point_injective
      rw [NormalizedIdealKleinTriangle.point_vertex]
      exact hpoint
    let x := r * t + c
    have hx : x ∈ Icc a b := by
      have hta := mul_le_mul_of_nonneg_left ht.1 hr.le
      have htb := mul_le_mul_of_nonneg_left ht.2 hr.le
      have hba := coord_back c r hr a
      have hbb := coord_back c r hr b
      constructor <;> dsimp only [x] <;> linarith
    have hcoord : coord c r x = t := by
      dsimp only [coord, x]
      field_simp [hr.ne']
      ring
    have hvertex : vertex (coord c r x) (coord_left hr (ha.trans_le hx.1))
        (coord_right hr (hx.2.trans_lt hb)) = w := by
      apply UpperHalfPlane.ext
      change NormalizedTriangleTangents.curve (coord c r x) = NormalizedTriangleTangents.curve t
      rw [hcoord]
    refine ⟨x, hx, ?_⟩
    rw [← affine_vertex, hvertex]
    rw [hw, smul_inv_smul]
  · rintro _ ⟨x, hx, rfl⟩
    exact graphPoint_between c r hr ha hb hab hx

end VeechDichotomy.CircularGeodesicArcs
