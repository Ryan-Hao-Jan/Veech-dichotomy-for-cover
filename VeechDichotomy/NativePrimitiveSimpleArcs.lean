module

public import VeechDichotomy.NativeRectangleCrossings

/-! Actual primitive charts construct embedded native horizontal
segments. Injectivity follows from the strictly advancing physical
coordinate, so it is not a geometric certificate supplied to the
rectangle-intersection argument. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePrimitiveSimpleArcs

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles
open Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem direction_injOn (i : Index q) (v : Plane) (hv : v ≠ 0) (x : Regular q)
    (hx : x ∈ (chart q i).source) (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, chart q i x + t • v ∈ (chart q i).target) : InjOn (trajectory q v x) I := by
  intro s hs t ht heq
  have hsline := (NativePrimitiveChartFlow.chart_trajectory q i v x hx I hI hord hzero hline hs).2
  have htline := (NativePrimitiveChartFlow.chart_trajectory q i v x hx I hI hord hzero hline ht).2
  have hcoords := congrArg (chart q i) heq
  rw [hsline, htline] at hcoords
  have hsmul : s • v = t • v := add_left_cancel hcoords
  have hzero' : (s - t) • v = 0 := by rw [sub_smul, hsmul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero').resolve_right hv)

theorem exists_direction_segment (i : Index q) (v : Plane) (hv : v ≠ 0) (x : Regular q)
    (hx : x ∈ (chart q i).source) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (-ε) ε ⊆ domain q v x ∧ InjOn (trajectory q v x) (Icc (-ε) ε) := by
  let D := MNEC.TranslationAtlasCurves.timeDomain (chart q i) v x
  have hD : IsOpen D := MNEC.TranslationAtlasCurves.timeDomain_open _ _ _
  have h0 : (0 : ℝ) ∈ D := MNEC.TranslationAtlasCurves.zero_mem_timeDomain _ _ _ hx
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hD 0 h0
  have hsmall : Icc (-(δ / 2)) (δ / 2) ⊆ Metric.ball (0 : ℝ) δ := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hrep := NativePrimitiveChartFlow.interval_representation q i v x hx (Metric.ball 0 δ) Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).ordConnected (Metric.mem_ball_self hδ) hsub
  have hinj := direction_injOn q i v hv x hx (Metric.ball 0 δ) Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).ordConnected (Metric.mem_ball_self hδ) hsub
  exact ⟨δ / 2, half_pos hδ, hsmall.trans hrep.1, hinj.mono hsmall⟩

theorem horizontal_injOn (i : Index q) (x : Regular q) (hx : x ∈ (chart q i).source)
    (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, chart q i x + t • horizontal ∈ (chart q i).target) :
    InjOn (trajectory q horizontal x) I := by
  intro s hs t ht heq
  have hsline := (NativePrimitiveChartFlow.chart_trajectory q i horizontal x hx I hI hord hzero hline hs).2
  have htline := (NativePrimitiveChartFlow.chart_trajectory q i horizontal x hx I hI hord hzero hline ht).2
  have hfirst := congrArg (fun y => (chart q i y).1) heq
  rw [hsline, htline, add_horizontal, add_horizontal] at hfirst
  exact add_left_cancel hfirst

theorem closed_segment (i : Index q) (x : Regular q) (hx : x ∈ (chart q i).source)
    (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, chart q i x + t • horizontal ∈ (chart q i).target)
    (a b : ℝ) (hab : Icc a b ⊆ I) :
    Icc a b ⊆ domain q horizontal x ∧ InjOn (trajectory q horizontal x) (Icc a b) :=
  ⟨hab.trans (NativePrimitiveChartFlow.interval_representation q i horizontal x hx I hI hord hzero hline).1,
    (horizontal_injOn q i x hx I hI hord hzero hline).mono hab⟩

theorem exists_segment (i : Index q) (x : Regular q) (hx : x ∈ (chart q i).source) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (-ε) ε ⊆ domain q horizontal x ∧
      InjOn (trajectory q horizontal x) (Icc (-ε) ε) := by
  let D := MNEC.TranslationAtlasCurves.timeDomain (chart q i) horizontal x
  have hD : IsOpen D := MNEC.TranslationAtlasCurves.timeDomain_open _ _ _
  have h0 : (0 : ℝ) ∈ D := MNEC.TranslationAtlasCurves.zero_mem_timeDomain _ _ _ hx
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hD 0 h0
  have hsmall : Icc (-(δ / 2)) (δ / 2) ⊆ Metric.ball (0 : ℝ) δ := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hseg := closed_segment q i x hx (Metric.ball 0 δ) Metric.isOpen_ball
    (convex_ball (0 : ℝ) δ).ordConnected (Metric.mem_ball_self hδ) hsub _ _ hsmall
  exact ⟨δ / 2, half_pos hδ, hseg.1, hseg.2⟩

end VeechDichotomy.NativePrimitiveSimpleArcs
