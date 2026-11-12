module

public import VeechDichotomy.ParameterSliceTransitions
public import VeechDichotomy.BeltramiMarkedFiberSurface
public import VeechDichotomy.HolomorphicCurveMaps

/-! A FIXED total chart gives genuine biholomorphic native fiber charts
on every nearby fiber, not only on the fiber at its center. This avoids
assuming continuity of a preferred chart chosen anew at each parameter. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFixedSlices

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def rawChart (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A) :
    OpenPartialHomeomorph Y ℂ :=
  ParameterSliceChart.chart Subtype.val Subtype.val_injective (BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2)
    (fun p _ => BeltramiMarkedFiberCharts.total_parameter π F hBranch s.1 s.2 p) a

def chart (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A) :
    OpenPartialHomeomorph (BeltramiMarkedFiberSurface.Surface π F hBranch a) ℂ :=
  (BeltramiMarkedFiberSurface.toOriginal π F hBranch a).transOpenPartialHomeomorph (rawChart π F hBranch s a)

theorem chart_source (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A)
    (y : BeltramiMarkedFiberSurface.Surface π F hBranch a) :
    y ∈ (chart π F hBranch s a).source ↔ (a, y.point) ∈ (BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2).source := Iff.rfl

theorem chart_target (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A) (z : ℂ) :
    z ∈ (chart π F hBranch s a).target ↔ (a.val, z) ∈ (BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2).target := Iff.rfl

theorem inverse_value (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A)
    {z : ℂ} (hz : z ∈ (chart π F hBranch s a).target) :
    (BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2).symm (a.val, z) =
      (a, ((chart π F hBranch s a).symm z).point) :=
  ParameterSliceChart.inverse_pair Subtype.val Subtype.val_injective (BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2)
    (fun p _ => BeltramiMarkedFiberCharts.total_parameter π F hBranch s.1 s.2 p) a hz

theorem raw_transition_holomorphic (s t : ComplexBeltramiMarkParameters.Parameters A × Y)
    (a : ComplexBeltramiMarkParameters.Parameters A) (z : ℂ)
    (hz : z ∈ ((rawChart π F hBranch s a).symm.trans (rawChart π F hBranch t a)).source) :
    ContDiffAt ℂ ω ((rawChart π F hBranch s a).symm.trans (rawChart π F hBranch t a)) z := by
  have hsource := ParameterSliceTransitions.transition_source Subtype.val Subtype.val_injective
    (BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2) (BeltramiMarkedFiberCharts.totalChart π F hBranch t.1 t.2)
    (fun p _ => BeltramiMarkedFiberCharts.total_parameter π F hBranch s.1 s.2 p)
    (fun p _ => BeltramiMarkedFiberCharts.total_parameter π F hBranch t.1 t.2 p) a hz
  have htotal : ContDiffAt ℂ ω
      ((BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2).symm.trans
        (BeltramiMarkedFiberCharts.totalChart π F hBranch t.1 t.2)) (a.val, z) :=
    HolomorphicCoverRelocationTransitions.rawChart_transition (BeltramiMarkedRelocationData.data π F hBranch) ⟨s⟩ ⟨t⟩ hsource
  exact ParameterSliceTransitions.transition_holomorphic Subtype.val Subtype.val_injective
    (BeltramiMarkedFiberCharts.totalChart π F hBranch s.1 s.2) (BeltramiMarkedFiberCharts.totalChart π F hBranch t.1 t.2)
    (fun p _ => BeltramiMarkedFiberCharts.total_parameter π F hBranch s.1 s.2 p)
    (fun p _ => BeltramiMarkedFiberCharts.total_parameter π F hBranch t.1 t.2 p) a z hz htotal

theorem holomorphicAt (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A)
    {y : BeltramiMarkedFiberSurface.Surface π F hBranch a} (hy : y ∈ (chart π F hBranch s a).source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chart π F hBranch s a) y := by
  let c := BeltramiMarkedFiberSurface.chart π F hBranch a y
  have hc := BeltramiMarkedFiberSurface.chart_center π F hBranch a y
  have hz : c y ∈ ((rawChart π F hBranch (a, y.point) a).symm.trans (rawChart π F hBranch s a)).source := by
    refine ⟨c.map_source hc, ?_⟩
    change c.symm (c y) ∈ (chart π F hBranch s a).source
    rwa [c.left_inv hc]
  apply HolomorphicCurveMaps.contMDiffAt_of_analytic_chart ((chart π F hBranch s a).continuousAt hy)
  exact (raw_transition_holomorphic π F hBranch (a, y.point) s a (c y) hz).analyticAt

theorem inverse_holomorphicAt (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A)
    {z : ℂ} (hz : z ∈ (chart π F hBranch s a).target) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chart π F hBranch s a).symm z := by
  let y := (chart π F hBranch s a).symm z
  have hsource : z ∈ ((rawChart π F hBranch s a).symm.trans (rawChart π F hBranch (a, y.point) a)).source :=
    ⟨hz, BeltramiMarkedFiberSurface.chart_center π F hBranch a y⟩
  apply HolomorphicCurveMaps.contMDiffAt_of_analytic_chart ((chart π F hBranch s a).symm.continuousAt hz)
  exact (raw_transition_holomorphic π F hBranch s (a, y.point) a z hsource).analyticAt

theorem chart_mem_maximalAtlas (s : ComplexBeltramiMarkParameters.Parameters A × Y) (a : ComplexBeltramiMarkParameters.Parameters A) :
    chart π F hBranch s a ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (BeltramiMarkedFiberSurface.Surface π F hBranch a) :=
  (chart π F hBranch s a).mem_maximalAtlas_of_contMDiffOn
    (fun _ hy => (holomorphicAt π F hBranch s a hy).contMDiffWithinAt)
    (fun _ hz => (inverse_holomorphicAt π F hBranch s a hz).contMDiffWithinAt)

end VeechDichotomy.BeltramiMarkedFixedSlices
