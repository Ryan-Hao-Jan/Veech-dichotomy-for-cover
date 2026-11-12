module

public import VeechDichotomy.MaximalTranslationCharts
public import MNEC.NativePrimitiveAreaCharts
public import MNEC.NativeCompleteDirectionalFlow

/-! Every actual native primitive chart carries the actual maximal
directional flow by straight coordinate lines. Representation is proved
on any open interval where the line remains in the chart, using native
integral-curve uniqueness, rather than an assumed flat-flow identity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePrimitiveChartFlow

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics
open MNEC Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem mem_translation_maximalAtlas (i : Index q) :
    letI := NativeRegularTranslationAtlas.chartedSpace q
    chart q i ∈ TranslationGroupoid.groupoid.maximalAtlas (Regular q) := by
  let := NativeRegularTranslationAtlas.chartedSpace q
  apply mem_maximalAtlas_iff.mpr
  intro e he
  change e ∈ range (coordinateChart q) at he
  obtain ⟨j, rfl⟩ := he
  rw [← chart_selected q j]
  constructor
  · exact ⟨NativePrimitiveAreaCharts.transition_locally_translation q i (selectedIndex q j),
      NativePrimitiveAreaCharts.transition_locally_translation q (selectedIndex q j) i⟩
  · exact ⟨NativePrimitiveAreaCharts.transition_locally_translation q (selectedIndex q j) i,
      NativePrimitiveAreaCharts.transition_locally_translation q i (selectedIndex q j)⟩

theorem interval_representation (i : Index q) (v : Plane) (x : Regular q)
    (hx : x ∈ (chart q i).source) (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, chart q i x + t • v ∈ (chart q i).target) :
    I ⊆ domain q v x ∧ ∀ t ∈ I, trajectory q v x t = (chart q i).symm (chart q i x + t • v) := by
  let := NativeRegularTranslationAtlas.chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact MaximalTranslationCharts.interval_representation (chart q i) (mem_translation_maximalAtlas q i)
    v x hx I hI hord hzero hline

theorem chart_trajectory (i : Index q) (v : Plane) (x : Regular q)
    (hx : x ∈ (chart q i).source) (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, chart q i x + t • v ∈ (chart q i).target) {t : ℝ} (ht : t ∈ I) :
    trajectory q v x t ∈ (chart q i).source ∧ chart q i (trajectory q v x t) = chart q i x + t • v := by
  rw [(interval_representation q i v x hx I hI hord hzero hline).2 t ht]
  exact ⟨(chart q i).map_target (hline t ht), (chart q i).right_inv (hline t ht)⟩

theorem primitive_trajectory (i : Index q) (v : Plane) (x : Regular q)
    (hx : x ∈ (chart q i).source) (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, chart q i x + t • v ∈ (chart q i).target) {t : ℝ} (ht : t ∈ I) :
    (trajectory q v x t).val = i.2.chart.symm (toPlane.symm (chart q i x + t • v)) := by
  rw [(interval_representation q i v x hx I hI hord hzero hline).2 t ht]
  exact chart_symm_value q i _ (hline t ht)

end VeechDichotomy.NativePrimitiveChartFlow
