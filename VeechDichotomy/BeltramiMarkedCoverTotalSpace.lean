module

public import VeechDichotomy.BeltramiMarkedRelocationData
public import VeechDichotomy.HolomorphicCoverRelocationSpace

/-! The actual simultaneous varying-base, moving-branch source total
space. Its complex structure is constructed by the checked relocation
atlas. The projection retains the original parameter/compact-source
topology, is proper, and is a holomorphic submersion. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedCoverTotalSpace

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

abbrev TotalSpace := HolomorphicCoverRelocationSpace.Source (BeltramiMarkedRelocationData.data π F hBranch)

def toReference : TotalSpace π F hBranch ≃ₜ BeltramiMarkedReferenceSpace.TotalSpace A qY :=
  HolomorphicCoverRelocationSpace.toOriginal (BeltramiMarkedRelocationData.data π F hBranch)

def toProduct : TotalSpace π F hBranch ≃ₜ ComplexBeltramiMarkParameters.Parameters A × Y :=
  (toReference π F hBranch).trans (BeltramiMarkedReferenceSpace.toProduct A qY)

def map : TotalSpace π F hBranch → BeltramiMarkedReferenceSpace.TotalSpace A qX :=
  HolomorphicCoverRelocationSpace.map (BeltramiMarkedRelocationData.data π F hBranch)

theorem map_point (z : TotalSpace π F hBranch) :
    (map π F hBranch z).point = ((toProduct π F hBranch z).1,
      BeltramiMarkedBaseTransport.transported F (toProduct π F hBranch z).1 (π.map (toProduct π F hBranch z).2)) := rfl

theorem holomorphic_map : ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) ω (map π F hBranch) :=
  HolomorphicCoverRelocationSpace.holomorphic_map (BeltramiMarkedRelocationData.data π F hBranch)

def projection (z : TotalSpace π F hBranch) : ComplexBeltramiMarkParameters.Parameters A :=
  (toProduct π F hBranch z).1

def ambientParameter (z : TotalSpace π F hBranch) : ComplexBeltramiMarkParameters.Space (m := m) :=
  (projection π F hBranch z).val

theorem proper_projection : IsProperMap (projection π F hBranch) :=
  isProperMap_fst_of_compactSpace.comp (toProduct π F hBranch).isProperMap

theorem projection_holomorphic : ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) ω (projection π F hBranch) := by
  intro z
  exact (BeltramiMarkedReferenceSpace.projection_holomorphic A qX _).comp z (holomorphic_map π F hBranch z)

theorem ambientParameter_holomorphic : ContMDiff 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) ω (ambientParameter π F hBranch) := by
  intro z
  exact (BeltramiMarkedReferenceSpace.ambientParameter_holomorphic A qX _).comp z (holomorphic_map π F hBranch z)

theorem rawChart_parameter (i z : BeltramiMarkedReferenceSpace.TotalSpace A qY) :
    (HolomorphicCoverRelocationTransitions.rawChart (BeltramiMarkedRelocationData.data π F hBranch) i z).1 = z.point.1.val := by
  by_cases hi : i ∈ (BeltramiMarkedRelocationData.data π F hBranch).critical
  · rw [HolomorphicCoverRelocationTransitions.rawChart, dite_eq_left hi]
    rfl
  · rw [HolomorphicCoverRelocationTransitions.rawChart, dite_eq_right hi]
    rfl

theorem chart_parameter (i z : TotalSpace π F hBranch) :
    (HolomorphicCoverRelocationSpace.chart (BeltramiMarkedRelocationData.data π F hBranch) i z).1 = ambientParameter π F hBranch z :=
  rawChart_parameter π F hBranch i.point z.point

theorem ambientParameter_surjective_derivative (z : TotalSpace π F hBranch) :
    Function.Surjective (mfderiv 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) (ambientParameter π F hBranch) z) := by
  let c := HolomorphicCoverRelocationSpace.chart (BeltramiMarkedRelocationData.data π F hBranch) z
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) c z :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
      (chart_mem_atlas _ z) (mem_chart_source _ z)
  have hf : HasMFDerivAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))
      (Prod.fst : ComplexBeltramiMarkParameters.Space (m := m) × ℂ → ComplexBeltramiMarkParameters.Space (m := m)) (c z)
      (ContinuousLinearMap.fst ℂ (ComplexBeltramiMarkParameters.Space (m := m)) ℂ) :=
    (ContinuousLinearMap.fst ℂ (ComplexBeltramiMarkParameters.Space (m := m)) ℂ).hasFDerivAt.hasMFDerivAt
  have hd := hf.comp z hc.hasMFDerivAt
  have heq : (Prod.fst ∘ c) = ambientParameter π F hBranch := funext fun w => chart_parameter π F hBranch z w
  rw [heq] at hd
  have hs := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ))
    (chart_mem_atlas _ z)).mfderiv_surjective (mem_chart_source _ z)
  rw [hd.mfderiv]
  intro v
  obtain ⟨u, hu⟩ := hs (v, 0)
  exact ⟨u, congrArg Prod.fst hu⟩

theorem projection_surjective_derivative (z : TotalSpace π F hBranch) :
    Function.Surjective (mfderiv 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) (projection π F hBranch) z) := by
  have hp := (projection_holomorphic π F hBranch).mdifferentiableAt (by decide) (x := z)
  have hc : MDifferentiableAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) (ComplexBeltramiMarkParameters.chart A) (projection π F hBranch z) :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)))
      (chart_mem_atlas _ (projection π F hBranch z)) (mem_chart_source _ (projection π F hBranch z))
  have hd : mfderiv 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) (ambientParameter π F hBranch) z =
      (mfderiv 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))
        𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) (ComplexBeltramiMarkParameters.chart A) (projection π F hBranch z)).comp
      (mfderiv 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
        𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) (projection π F hBranch) z) :=
    (hc.hasMFDerivAt.comp z hp.hasMFDerivAt).mfderiv
  have hi := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)))
    (chart_mem_atlas _ (projection π F hBranch z))).mfderiv_injective (mem_chart_source _ (projection π F hBranch z))
  intro v
  obtain ⟨u, hu⟩ := ambientParameter_surjective_derivative π F hBranch z
    (mfderiv 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m))
      𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m)) (ComplexBeltramiMarkParameters.chart A) (projection π F hBranch z) v)
  refine ⟨u, hi ?_⟩
  rw [hd] at hu
  exact hu

end VeechDichotomy.BeltramiMarkedCoverTotalSpace
