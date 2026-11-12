module

public import VeechDichotomy.BeltramiMarkedReferenceTransitions

/-! A constructed proper complex reference family over the full
structure/displacement domain. Its topology is the original parameter
times compact surface topology, and forgetting the displacement coordinates
is a genuinely holomorphic map to the native Beltrami total family. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedReferenceSpace

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {qX : Differential X} {b : Fin m → X} {μ₀ : Parameter}
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

structure TotalSpace (A : Data qX b μ₀) (qY : Differential Y) where
  point : ComplexBeltramiMarkParameters.Parameters A × Y

variable (A : Data qX b μ₀) (qY : Differential Y)

instance topology : TopologicalSpace (TotalSpace A qY) := TopologicalSpace.induced TotalSpace.point inferInstance

def toProduct : TotalSpace A qY ≃ₜ ComplexBeltramiMarkParameters.Parameters A × Y where
  toFun := TotalSpace.point
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space : T2Space (TotalSpace A qY) := (toProduct A qY).isEmbedding.t2Space

def chart (z : TotalSpace A qY) : OpenPartialHomeomorph (TotalSpace A qY)
    (ComplexBeltramiMarkParameters.Space (m := m) × ℂ) :=
  (toProduct A qY).transOpenPartialHomeomorph (BeltramiMarkedReferenceCharts.chart A qY z.point.2)

theorem chart_center (z : TotalSpace A qY) : z ∈ (chart A qY z).source :=
  BeltramiMarkedReferenceCharts.chart_center A qY z.point.1 z.point.2

theorem transition_holomorphicOn (i j : TotalSpace A qY) :
    ContDiffOn ℂ ω ((chart A qY i).symm.trans (chart A qY j)) ((chart A qY i).symm.trans (chart A qY j)).source := by
  change ContDiffOn ℂ ω
    ((BeltramiMarkedReferenceCharts.chart A qY i.point.2).symm.trans (BeltramiMarkedReferenceCharts.chart A qY j.point.2))
    ((BeltramiMarkedReferenceCharts.chart A qY i.point.2).symm.trans (BeltramiMarkedReferenceCharts.chart A qY j.point.2)).source
  exact BeltramiMarkedReferenceTransitions.transition_holomorphicOn A qY i.point.2 j.point.2

@[instance_reducible] def chartedSpace : ChartedSpace (ComplexBeltramiMarkParameters.Space (m := m) × ℂ) (TotalSpace A qY) where
  atlas := range (chart A qY)
  chartAt := chart A qY
  mem_chart_source := chart_center A qY
  chart_mem_atlas z := ⟨z, rfl⟩

theorem isComplexManifold : letI := chartedSpace A qY
    IsManifold 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (TotalSpace A qY) := by
  let := chartedSpace A qY
  let : HasGroupoid (TotalSpace A qY) (contDiffGroupoid ω 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ω 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
    intro e f he hf
    change e ∈ range (chart A qY) at he
    change f ∈ range (chart A qY) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    simpa only [contDiffPregroupoid, mfld_simps] using transition_holomorphicOn A qY i j
  exact IsManifold.mk' 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (TotalSpace A qY)

attribute [instance] chartedSpace isComplexManifold

def projection (z : TotalSpace A qY) : ComplexBeltramiMarkParameters.Parameters A := z.point.1

def ambientParameter (z : TotalSpace A qY) : ComplexBeltramiMarkParameters.Space (m := m) := z.point.1.val

theorem proper_projection : IsProperMap (projection A qY) :=
  isProperMap_fst_of_compactSpace.comp (toProduct A qY).isProperMap

theorem chart_parameter (i z : TotalSpace A qY) : (chart A qY i z).1 = ambientParameter A qY z := rfl

theorem ambientParameter_holomorphic : ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) ω (ambientParameter A qY) := by
  intro z
  have hc : ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (chart A qY z) z :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas z) (chart_center A qY z)
  exact (contDiff_fst.contMDiff _).comp z hc

theorem projection_holomorphic : ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) ω (projection A qY) := by
  intro z
  have ht : ambientParameter A qY z ∈ (ComplexBeltramiMarkParameters.chart A).target := by
    rw [ComplexBeltramiMarkParameters.chart_target]
    exact z.point.1.property
  have hInv : ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) ω (ComplexBeltramiMarkParameters.chart A).symm
      (ambientParameter A qY z) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas z.point.1) ht
  apply (hInv.comp z (ambientParameter_holomorphic A qY z)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun w =>
    ((ComplexBeltramiMarkParameters.chart A).left_inv (mem_univ w.point.1)).symm

def realization (z : TotalSpace A qY) : NativeBeltramiTotalSpace.TotalSpace qY :=
  BeltramiMarkedReferenceCharts.realization A qY z.point

theorem continuous_realization : Continuous (realization A qY) :=
  (BeltramiMarkedReferenceCharts.continuous_realization A qY).comp (toProduct A qY).continuous

theorem realization_holomorphic : ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    𝓘(ℂ, ℂ × ℂ) ω (realization A qY) := by
  intro z
  have hc : ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (chart A qY z) z :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas z) (chart_center A qY z)
  have hInv := BeltramiMarkedReferenceTransitions.inverse_realization_holomorphic A qY z.point.2
    ((BeltramiMarkedReferenceCharts.chart A qY z.point.2).map_source (chart_center A qY z))
  apply (hInv.comp z hc).congr_of_eventuallyEq
  filter_upwards [(chart A qY z).open_source.mem_nhds (chart_center A qY z)] with w hw
  exact congrArg (BeltramiMarkedReferenceCharts.realization A qY)
    ((BeltramiMarkedReferenceCharts.chart A qY z.point.2).left_inv hw).symm

end VeechDichotomy.BeltramiMarkedReferenceSpace
