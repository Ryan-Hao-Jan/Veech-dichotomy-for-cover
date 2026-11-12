module

public import MNEC.NativeDifferentialEquiv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-! The local Cauchy theorem upgrades complex differentiability between
complex curves to analytic manifold smoothness. Adapted from the supplied
NativeHolomorphicSmooth proof and its small chart bridge; the unrelated
degree-one sphere imports are unnecessary here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicCurveMaps

open Set Filter Topology
open scoped Manifold ContDiff

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
theorem contMDiffAt_of_analytic_chart {F : X → Y} {x : X} (hc : ContinuousAt F x)
    (ha : AnalyticAt ℂ ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x := by
  rw [contMDiffAt_iff]
  refine ⟨hc, ?_⟩
  have hr : Set.range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hr, contDiffWithinAt_univ]
  have hbase : extChartAt 𝓘(ℂ) x x = (chartAt ℂ x) x := by simp
  have hfun : (extChartAt 𝓘(ℂ) (F x) ∘ F ∘ (extChartAt 𝓘(ℂ) x).symm) =
      ((chartAt ℂ (F x)) ∘ F ∘ (chartAt ℂ x).symm) := by funext z; simp
  rw [hfun, hbase]
  exact ha.contDiffAt

theorem contMDiff_of_mdifferentiable (F : X → Y)
    (hF : ∀ x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F x) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  intro x
  apply contMDiffAt_of_analytic_chart (hF x).continuousAt
  let e := chartAt ℂ x
  let g := chartAt ℂ (F x)
  let U : Set ℂ := e.target ∩ (F ∘ e.symm) ⁻¹' g.source
  have hU : IsOpen U :=
    (hc.comp_continuousOn e.symm.continuousOn).isOpen_inter_preimage e.open_target g.open_source
  have hx : e x ∈ U := by
    refine ⟨e.map_source (mem_chart_source ℂ x), ?_⟩
    change F (e.symm (e x)) ∈ g.source
    rw [e.left_inv (mem_chart_source ℂ x)]
    exact mem_chart_source ℂ (F x)
  have hd : DifferentiableOn ℂ (g ∘ F ∘ e.symm) U := by
    intro z hz
    have he := mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ x) hz.1
    have hg := mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (F x)) hz.2
    exact (hg.comp z ((hF (e.symm z)).comp z he)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hx)

end VeechDichotomy.HolomorphicCurveMaps
