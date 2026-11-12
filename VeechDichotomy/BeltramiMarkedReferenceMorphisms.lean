module

public import VeechDichotomy.BeltramiMarkedReferenceSpace

/-! A map into the constructed reference family is holomorphic when
its actual parameter map and actual native-family realization are
holomorphic. This follows from the explicit target charts. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedReferenceMorphisms

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData BeltramiMarkedReferenceSpace
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {qX : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data qX b μ₀)
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] (qY : Differential Y)
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem holomorphicAt_of_realization (f : M → TotalSpace A qY) (z : M)
    (hcontinuous : ContinuousAt f z)
    (hparameter : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) ω
      (fun w => ambientParameter A qY (f w)) z)
    (hnative : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ × ℂ) ω (fun w => realization A qY (f w)) z) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω f z := by
  let c := NativeBeltramiTotalSpace.chart qY ⟨(μ₀, (f z).point.2)⟩
  have hc : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω c (realization A qY (f z)) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (⟨(μ₀, (f z).point.2)⟩ : NativeBeltramiTotalSpace.TotalSpace qY))
      ((NativeBeltramiCharts.chart_source qY (f z).point.2 _).mpr (NativePowerCharts.chosen qY (f z).point.2).center)
  have hcomp := hc.comp z hnative
  have hs : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω (fun w => (c (realization A qY (f w))).2) z :=
    (contDiff_snd.contMDiff _).comp z hcomp
  rw [contMDiffAt_iff_target_of_mem_source (y := f z) (chart_center A qY (f z))]
  exact ⟨hcontinuous, hparameter.prodMk_space hs⟩

end VeechDichotomy.BeltramiMarkedReferenceMorphisms
