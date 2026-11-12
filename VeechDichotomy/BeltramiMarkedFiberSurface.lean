module

public import VeechDichotomy.BeltramiMarkedFiberCharts

/-! Genuine compact connected native complex curves on the actual
fibers of the varying-base moved-cover family. Their complex atlas is
the slice of the constructed total atlas, and their inclusions are
holomorphic embeddings onto the actual projection fibers. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberSurface

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

structure Surface (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A)
    (hBranch : range b = branchValues π) (a : ComplexBeltramiMarkParameters.Parameters A) where
  point : Y

variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
  (a : ComplexBeltramiMarkParameters.Parameters A)

instance topology : TopologicalSpace (Surface π F hBranch a) := TopologicalSpace.induced Surface.point inferInstance

def toOriginal : Surface π F hBranch a ≃ₜ Y where
  toFun := Surface.point
  invFun y := ⟨y⟩
  left_inv y := by cases y; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space : T2Space (Surface π F hBranch a) := (toOriginal π F hBranch a).isEmbedding.t2Space
instance compactSpace : CompactSpace (Surface π F hBranch a) := (toOriginal π F hBranch a).symm.compactSpace
instance connectedSpace : ConnectedSpace (Surface π F hBranch a) :=
  (toOriginal π F hBranch a).symm.surjective.connectedSpace (toOriginal π F hBranch a).symm.continuous

def chart (i : Surface π F hBranch a) : OpenPartialHomeomorph (Surface π F hBranch a) ℂ :=
  (toOriginal π F hBranch a).transOpenPartialHomeomorph (BeltramiMarkedFiberCharts.chart π F hBranch a i.point)

theorem chart_center (i : Surface π F hBranch a) : i ∈ (chart π F hBranch a i).source :=
  BeltramiMarkedFiberCharts.chart_center π F hBranch a i.point

theorem transition_holomorphicOn (i j : Surface π F hBranch a) :
    ContDiffOn ℂ ω ((chart π F hBranch a i).symm.trans (chart π F hBranch a j))
      ((chart π F hBranch a i).symm.trans (chart π F hBranch a j)).source := by
  change ContDiffOn ℂ ω ((BeltramiMarkedFiberCharts.chart π F hBranch a i.point).symm.trans
    (BeltramiMarkedFiberCharts.chart π F hBranch a j.point))
    ((BeltramiMarkedFiberCharts.chart π F hBranch a i.point).symm.trans (BeltramiMarkedFiberCharts.chart π F hBranch a j.point)).source
  exact BeltramiMarkedFiberCharts.transition_holomorphicOn π F hBranch a i.point j.point

@[instance_reducible] def chartedSpace : ChartedSpace ℂ (Surface π F hBranch a) where
  atlas := range (chart π F hBranch a)
  chartAt := chart π F hBranch a
  mem_chart_source := chart_center π F hBranch a
  chart_mem_atlas y := ⟨y, rfl⟩

theorem isComplexManifold : letI := chartedSpace π F hBranch a
    IsManifold 𝓘(ℂ) ω (Surface π F hBranch a) := by
  let := chartedSpace π F hBranch a
  let : HasGroupoid (Surface π F hBranch a) (contDiffGroupoid ω 𝓘(ℂ)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ω 𝓘(ℂ))
    intro e f he hf
    change e ∈ range (chart π F hBranch a) at he
    change f ∈ range (chart π F hBranch a) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    simpa only [contDiffPregroupoid, mfld_simps] using transition_holomorphicOn π F hBranch a i j
  exact IsManifold.mk' 𝓘(ℂ) ω (Surface π F hBranch a)

attribute [instance] chartedSpace isComplexManifold

def inclusion (y : Surface π F hBranch a) : BeltramiMarkedCoverTotalSpace.TotalSpace π F hBranch :=
  (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).symm (a, y.point)

theorem continuous_inclusion : Continuous (inclusion π F hBranch a) :=
  (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).symm.continuous.comp
    (continuous_const.prodMk (toOriginal π F hBranch a).continuous)

theorem projection_inclusion (y : Surface π F hBranch a) :
    BeltramiMarkedCoverTotalSpace.projection π F hBranch (inclusion π F hBranch a y) = a := rfl

def fiberHomeomorph : Surface π F hBranch a ≃ₜ
    (BeltramiMarkedCoverTotalSpace.projection π F hBranch ⁻¹' {a}) where
  toFun y := ⟨inclusion π F hBranch a y, rfl⟩
  invFun y := ⟨(BeltramiMarkedCoverTotalSpace.toProduct π F hBranch y.val).2⟩
  left_inv _ := rfl
  right_inv y := by
    apply Subtype.ext
    apply (BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).injective
    exact Prod.ext y.property.symm rfl
  continuous_toFun := (continuous_inclusion π F hBranch a).subtype_mk _
  continuous_invFun := (toOriginal π F hBranch a).symm.continuous.comp
    (continuous_snd.comp ((BeltramiMarkedCoverTotalSpace.toProduct π F hBranch).continuous.comp continuous_subtype_val))

theorem chart_value (i y : Surface π F hBranch a) :
    HolomorphicCoverRelocationSpace.chart (BeltramiMarkedRelocationData.data π F hBranch)
      (inclusion π F hBranch a i) (inclusion π F hBranch a y) = (a.val, chart π F hBranch a i y) :=
  BeltramiMarkedFiberCharts.total_value π F hBranch a i.point y.point

theorem holomorphic_inclusion : ContMDiff 𝓘(ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (inclusion π F hBranch a) := by
  intro y
  rw [contMDiffAt_iff_target_of_mem_source (y := inclusion π F hBranch a y)
    (mem_chart_source (ComplexBeltramiMarkParameters.Space (m := m) × ℂ) (inclusion π F hBranch a y))]
  refine ⟨(continuous_inclusion π F hBranch a).continuousAt, ?_⟩
  have heq : (extChartAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      (inclusion π F hBranch a y) ∘ inclusion π F hBranch a) =
      fun w => (a.val, chart π F hBranch a y w) := funext fun w => chart_value π F hBranch a y w
  rw [heq]
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) ω
      (fun _ : Surface π F hBranch a => a.val) y := contMDiffAt_const
  have hy : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chart π F hBranch a y) y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y) (chart_center π F hBranch a y)
  exact hc.prodMk_space hy

end VeechDichotomy.BeltramiMarkedFiberSurface
