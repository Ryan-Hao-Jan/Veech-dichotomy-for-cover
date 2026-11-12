module

public import MNEC.NativeRegularTranslationAtlas
public import MNEC.TranslationAtlasCurves

/-! Native derivative and flow formulas for every compatible physical
translation chart, including genuine primitive charts outside the
selected pointwise atlas. All coordinate derivatives are derived from
actual local translation germs. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.MaximalTranslationCharts

open MNEC.LatticeTorus MNEC Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable (e : OpenPartialHomeomorph M Plane) (he : e ∈ TranslationGroupoid.groupoid.maximalAtlas M)

include he in
theorem mem_smooth_maximalAtlas (n : ℕ∞ω) : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) n M :=
  StructureGroupoid.maximalAtlas_mono (NativeRegularTranslationAtlas.translationGroupoid_le_contDiffGroupoid n) he

include he in
theorem mdifferentiable : e.MDifferentiable 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) :=
  ⟨fun _ hx => (mdifferentiableAt_of_mem_maximalAtlas (mem_smooth_maximalAtlas e he 1) hx).mdifferentiableWithinAt,
    fun _ hx => (mdifferentiableAt_symm_of_mem_maximalAtlas (mem_smooth_maximalAtlas e he 1) hx).mdifferentiableWithinAt⟩

include he in
theorem mfderiv_eq_id {x : M} (hx : x ∈ e.source) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e x = ContinuousLinearMap.id ℝ Plane := by
  let c := chartAt Plane x
  have hxc : x ∈ c.source := mem_chart_source Plane x
  have hp : c x ∈ (c.symm.trans e).source := by
    refine ⟨c.map_source hxc, ?_⟩
    change c.symm (c x) ∈ e.source
    rwa [c.left_inv hxc]
  have hgroup := TranslationGroupoid.groupoid.compatible_of_mem_maximalAtlas_right (x := x) he
  obtain ⟨a, ha⟩ := ((TranslationGroupoid.mem_groupoid_iff _).mp hgroup).1 (c x) hp
  have htransition : HasFDerivAt (c.symm.trans e) (ContinuousLinearMap.id ℝ Plane) (c x) :=
    ((hasFDerivAt_id (c x)).add_const a).congr_of_eventuallyEq ha
  have hd := (mdifferentiable e he).mdifferentiableAt hx
  rw [hd.mfderiv_abuse]
  simpa only [writtenInExtChartAt, extChartAt, mfld_simps, fderivWithin_univ, c] using! htransition.fderiv

include he in
theorem mfderiv_symm_eq_id {z : Plane} (hz : z ∈ e.target) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) e.symm z = ContinuousLinearMap.id ℝ Plane := by
  have hcomp := (mdifferentiable e he).comp_symm_deriv hz
  rw [mfderiv_eq_id e he (e.map_target hz)] at hcomp
  simpa only [ContinuousLinearMap.id_comp] using! hcomp

include he in
theorem hasMFDerivAt_curve (v : Plane) (x : M) {t : ℝ}
    (ht : t ∈ TranslationAtlasCurves.timeDomain e v x) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) (TranslationAtlasCurves.curve e v x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  let line := fun s : ℝ => e x + s • v
  have hline : HasDerivAt line v t := by
    simpa [line] using! ((hasDerivAt_id t).smul_const v).const_add (e x)
  have hlineM := hline.hasFDerivAt.hasMFDerivAt
  have hi := ((mdifferentiable e he).mdifferentiableAt_symm ht).hasMFDerivAt
  rw [mfderiv_symm_eq_id e he ht] at hi
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def, TranslationAtlasCurves.curve, line] using! hi.comp t hlineM

variable [IsManifold 𝓘(ℝ, Plane) ∞ M] [HasGroupoid M TranslationGroupoid.groupoid]

include he in
theorem isMIntegralCurveOn_curve (v : Plane) (x : M) :
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (TranslationAtlasCurves.curve e v x)
      (TranslationAtlasField.field v) (TranslationAtlasCurves.timeDomain e v x) := by
  intro t ht
  rw [TranslationAtlasField.field_eq_const]
  exact (hasMFDerivAt_curve e he v x ht).hasMFDerivWithinAt

variable [T2Space M]

include he in
theorem interval_representation (v : Plane) (x : M) (hx : x ∈ e.source)
    (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, e x + t • v ∈ e.target) :
    I ⊆ TranslationAtlasCurves.domain v x ∧
      ∀ t ∈ I, TranslationAtlasCurves.trajectory v x t = e.symm (e x + t • v) :=
  TranslationAtlasCurves.extends_every_open_interval v x I (TranslationAtlasCurves.curve e v x)
    hI hord hzero (TranslationAtlasCurves.curve_zero e v x hx)
    ((isMIntegralCurveOn_curve e he v x).mono hline)

end VeechDichotomy.MaximalTranslationCharts
