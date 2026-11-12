module

public import MNEC.NativeAbelianDifferential
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

@[expose] public section

open scoped Manifold ContDiff Topology Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MNEC.RegularPrimitiveCharts

open Set Filter Metric NativeAbelianDifferential

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- At every actual regular point the fixed-chart coefficient has a genuine
holomorphic primitive with nonzero derivative throughout a neighborhood. -/
theorem exists_local_primitive (q : Differential X) (x : X) (hx : x ∈ regularSet q) :
    ∃ r : ℝ, 0 < r ∧ ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target ∧
      ∃ F : ℂ → ℂ, ∀ z ∈ ball ((chartAt ℂ x) x) r,
        HasDerivAt F (Jacobians.NativeCanonical.coeffAt q.val x z) z ∧
          Jacobians.NativeCanonical.coeffAt q.val x z ≠ 0 := by
  let a := (chartAt ℂ x) x
  let c := Jacobians.NativeCanonical.coeffAt q.val x
  have ha : a ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have han : AnalyticAt ℂ c a := Jacobians.NativeCanonical.coeffAt_analyticAt q.val x ha
  have hc : c a ≠ 0 := by
    rw [show c a = Jacobians.Montel.localRep q.val x x from
      Jacobians.NativeCanonical.coeffAt_self_eq_localRep q.val x]
    exact fun h => hx ((toFun_eq_zero_iff_localRep_self q x).mpr h)
  have hn : (chartAt ℂ x).target ∩ {z | c z ≠ 0} ∈ 𝓝 a :=
    inter_mem ((chartAt ℂ x).open_target.mem_nhds ha)
      (han.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hc))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  have htarget : ball a r ⊆ (chartAt ℂ x).target := fun z hz => (hball hz).1
  have hcder : DifferentiableOn ℂ c (ball a r) := fun z hz =>
    (Jacobians.NativeCanonical.coeffAt_analyticAt q.val x (htarget hz)).differentiableWithinAt
  obtain ⟨F, hF⟩ := (convex_ball a r).exists_forall_hasDerivWithinAt hcder
  refine ⟨r, hr, htarget, F, fun z hz => ?_⟩
  exact ⟨(hF z hz).hasDerivAt (isOpen_ball.mem_nhds hz), (hball hz).2⟩

/-- A genuine primitive coordinate homeomorphism at each actual regular point.
The map, its open domain, and its primitive formula are constructed using the
complex inverse function theorem. -/
theorem exists_primitive_chart (q : Differential X) (x : X) (hx : x ∈ regularSet q) :
    ∃ e : OpenPartialHomeomorph X ℂ, x ∈ e.source ∧ e.source ⊆ regularSet q ∧
      ∃ F : ℂ → ℂ, ∀ y ∈ e.source,
        y ∈ (chartAt ℂ x).source ∧ e y = F ((chartAt ℂ x) y) ∧
          HasDerivAt F (Jacobians.NativeCanonical.coeffAt q.val x ((chartAt ℂ x) y))
            ((chartAt ℂ x) y) := by
  obtain ⟨r, hr, htarget, F, hF⟩ := exists_local_primitive q x hx
  let a := (chartAt ℂ x) x
  have ha : a ∈ ball a r := mem_ball_self hr
  have hdiff : DifferentiableOn ℂ F (ball a r) := fun z hz =>
    (hF z hz).1.differentiableAt.differentiableWithinAt
  have han : AnalyticAt ℂ F a := hdiff.analyticAt (isOpen_ball.mem_nhds ha)
  have hstrict : HasStrictDerivAt F (Jacobians.NativeCanonical.coeffAt q.val x a) a := by
    convert han.hasStrictDerivAt using 1
    exact (hF a ha).1.deriv.symm
  let R := (hstrict.hasStrictFDerivAt_equiv (hF a ha).2).toOpenPartialHomeomorph F
  have haR : a ∈ R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  let E := R.restr (ball a r)
  have haE : a ∈ E.source := by
    simpa only [E, OpenPartialHomeomorph.restr_source, isOpen_ball.interior_eq] using ⟨haR, ha⟩
  let e := (chartAt ℂ x).trans E
  have hex : x ∈ e.source := ⟨mem_chart_source ℂ x, haE⟩
  have hcoord (y : X) (hy : y ∈ e.source) : (chartAt ℂ x) y ∈ ball a r := by
    have h := hy.2
    change (chartAt ℂ x) y ∈ E.source at h
    simpa only [E, OpenPartialHomeomorph.restr_source, isOpen_ball.interior_eq] using h.2
  have heq (y : X) : e y = F ((chartAt ℂ x) y) := by
    change R ((chartAt ℂ x) y) = _
    exact congrFun (HasStrictFDerivAt.toOpenPartialHomeomorph_coe _) _
  refine ⟨e, hex, ?_, F, fun y hy => ⟨hy.1, heq y, (hF _ (hcoord y hy)).1⟩⟩
  intro y hy hzero
  have hnonzero := (hF _ (hcoord y hy)).2
  apply hnonzero
  change Jacobians.Montel.localRep q.val x ((chartAt ℂ x).symm ((chartAt ℂ x) y)) = 0
  rw [(chartAt ℂ x).left_inv hy.1]
  exact Jacobians.NativeCanonical.localRep_eq_zero_of_toFun_eq_zero q.val x hzero

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem extChartAt_coe_eq_chart (x : X) :
    (extChartAt 𝓘(ℂ) x : X → ℂ) = chartAt ℂ x := by
  simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, OpenPartialHomeomorph.coe_toPartialEquiv]

/-- Intrinsic cotangent value expressed in one fixed native chart. -/
theorem toFun_eq_coeffAt_smul_mfderiv (q : Differential X) (x y : X)
    (hy : y ∈ (chartAt ℂ x).source) :
    q.val.toFun y = Jacobians.NativeCanonical.coeffAt q.val x ((chartAt ℂ x) y) •
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y := by
  have h := Jacobians.Montel.toFun_eq_localRep_smul q.val x y hy
  rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq',
    TangentBundle.continuousLinearMapAt_trivializationAt hy, extChartAt_coe_eq_chart] at h
  simpa only [Jacobians.NativeCanonical.coeffAt, (chartAt ℂ x).left_inv hy] using h

/-- Actual translation coordinates for an arbitrary native Abelian differential:
the differential of the constructed coordinate is the original cotangent form. -/
theorem exists_native_translation_chart (q : Differential X) (x : X)
    (hx : x ∈ regularSet q) :
    ∃ e : OpenPartialHomeomorph X ℂ, x ∈ e.source ∧ e.source ⊆ regularSet q ∧
      ∀ y ∈ e.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) e y (q.val.toFun y) := by
  obtain ⟨e, hex, hregular, F, he⟩ := exists_primitive_chart q x hx
  refine ⟨e, hex, hregular, fun y hy => ?_⟩
  obtain ⟨hysrc, heq, hF⟩ := he y hy
  let c := Jacobians.NativeCanonical.coeffAt q.val x ((chartAt ℂ x) y)
  have hDF : HasFDerivAt F (c • ContinuousLinearMap.id ℂ ℂ) ((chartAt ℂ x) y) := by
    apply hasFDerivAt_iff_hasDerivAt.mpr
    simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hF
  have hchart := ((mdifferentiable_chart (I := 𝓘(ℂ)) x).mdifferentiableAt hysrc).hasMFDerivAt
  have hcomp := hDF.hasMFDerivAt.comp y hchart
  have hmap : (c • ContinuousLinearMap.id ℂ ℂ).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y) = q.val.toFun y := by
    rw [toFun_eq_coeffAt_smul_mfderiv q x y hysrc]
    rfl
  rw [hmap] at hcomp
  have hevent : (e : X → ℂ) =ᶠ[𝓝 y] F ∘ (chartAt ℂ x) := by
    filter_upwards [e.open_source.mem_nhds hy] with z hz
    exact (he z hz).2.1
  exact hcomp.congr_of_eventuallyEq hevent

end MNEC.RegularPrimitiveCharts

