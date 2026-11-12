module

public import VeechDichotomy.FiniteTriangleNormalization

/-! Actual triangles on a common complete hyperbolic geodesic have
actual area zero. Metric betweenness proves vertical-line convexity;
the constructed actual SL2 normalization and area invariance reduce
the full triangle to a literal null vertical set. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CollinearHyperbolicTriangles

open LinearGroup Set MeasureTheory HyperbolicTripleNormalization HyperbolicGeodesicHulls
open HyperbolicGeodesicLines HyperbolicMetricSegments HyperbolicTriangles
open scoped UpperHalfPlane

theorem vertical_geodesicallyConvex (d : ℝ) : GeodesicallyConvex {z : ℍ | z.re = d} := by
  intro a ha b hb z hz
  have hpoint (u : ℍ) (hu : u.re = d) : verticalPoint d (Real.log u.im) = u := by
    apply UpperHalfPlane.ext_re_im
    · exact hu.symm
    · exact Real.exp_log u.im_pos
  have hz' : dist (verticalPoint d (Real.log a.im)) z + dist z (verticalPoint d (Real.log b.im)) =
      dist (verticalPoint d (Real.log a.im)) (verticalPoint d (Real.log b.im)) := by
    rw [hpoint a ha, hpoint b hb]
    exact hz
  exact ((vertical_between_iff d (Real.log a.im) (Real.log b.im) z).mp hz').1

theorem vertical_null (d : ℝ) : volume {z : ℍ | z.re = d} = 0 :=
  HyperbolicBisectorNull.volume_preimage_null (ComplexQuadraticNull.vertical_null d)

theorem area_zero {a b c : ℍ} (h : OnCommonGeodesic a b c) : volume (triangle a b c) = 0 := by
  obtain ⟨A, d, ha, hb, hc⟩ := h
  have hsub : triangle (A • a) (A • b) (A • c) ⊆ {z : ℍ | z.re = d} :=
    triangle_subset (vertical_geodesicallyConvex d) ha hb hc
  have hz : volume (triangle (A • a) (A • b) (A • c)) = 0 :=
    measure_mono_null hsub (vertical_null d)
  have hm : volume (triangle (A • a) (A • b) (A • c)) = volume (triangle a b c) := by
    rw [← image_triangle_smul]
    exact measure_smul (volume : Measure ℍ) A _
  exact hm.symm.trans hz

theorem real_area_zero {a b c : ℍ} (h : OnCommonGeodesic a b c) :
    (volume (triangle a b c)).toReal = 0 := by rw [area_zero h, ENNReal.toReal_zero]

end VeechDichotomy.CollinearHyperbolicTriangles
