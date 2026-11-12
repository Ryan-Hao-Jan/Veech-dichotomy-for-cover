module

public import VeechDichotomy.NativeBeltramiFibers

/-! Every fixed underlying point defines an actual holomorphic section
of the analytic deformation family, including points at differential
zeros. Its preferred power coordinate is zero for every parameter. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiMarkedSections

open MNEC.NativeAbelianDifferential BeltramiPlane Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (b : X)

def sectionMap (μ : Parameter) : NativeBeltramiTotalSpace.TotalSpace q := ⟨(μ, b)⟩

theorem projection_section (μ : Parameter) : NativeBeltramiTotalSpace.projection q (sectionMap q b μ) = μ := rfl

theorem continuous_section : Continuous (sectionMap q b) :=
  (NativeBeltramiTotalSpace.toProduct q).symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem chart_section (μ ν : Parameter) :
    NativeBeltramiTotalSpace.chart q (sectionMap q b μ) (sectionMap q b ν) = (ν.val, 0) := by
  change NativeBeltramiCharts.chart q b (ν, b) = (ν.val, 0)
  rw [NativeBeltramiCharts.chart_apply, (NativePowerCharts.chosen q b).center_zero, BeltramiPowerLift.rootHomeomorph_zero]

theorem holomorphic_section : ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ω (sectionMap q b) := by
  intro μ
  rw [contMDiffAt_iff_target_of_mem_source (y := sectionMap q b μ) (mem_chart_source (ℂ × ℂ) (sectionMap q b μ))]
  refine ⟨(continuous_section q b).continuousAt, ?_⟩
  have heq : (extChartAt 𝓘(ℂ, ℂ × ℂ) (sectionMap q b μ) ∘ sectionMap q b) = fun ν : Parameter => (ν.val, 0) := by
    funext ν
    exact chart_section q b μ ν
  rw [heq]
  have hval : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : Parameter → ℂ) μ :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas μ) (mem_univ μ)
  have hzero : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun _ : Parameter => (0 : ℂ)) μ := contMDiffAt_const
  exact hval.prodMk_space hzero

end VeechDichotomy.NativeBeltramiMarkedSections
