module

public import VeechDichotomy.NativeAnalyticCoverTransitions
public import VeechDichotomy.ComplexDisplacementManifold
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Topology.Maps.Proper.Basic

/-! The moving cover family has a constructed analytic complex total
space with the ACTUAL product topology. Its projection to displacement
parameters is proper, and its ambient complex parameter coordinate is
holomorphic. No moduli-space topology or properness oracle is supplied. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverTotalSpace

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open ComplexDisplacementParameters NativeAnalyticCoverTransitions Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}

structure TotalSpace (π : Cover ωX ωY) {b : Fin m → X} (A : Data b) (hBranch : range b = branchValues π) where
  point : Parameters m × Y

variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b) (hBranch : range b = branchValues π)

instance topology : TopologicalSpace (TotalSpace π A hBranch) := TopologicalSpace.induced TotalSpace.point inferInstance

def toProduct : TotalSpace π A hBranch ≃ₜ Parameters m × Y where
  toFun := TotalSpace.point
  invFun := fun p => ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space : T2Space (TotalSpace π A hBranch) := (toProduct π A hBranch).isEmbedding.t2Space

def chart (i : TotalSpace π A hBranch) : OpenPartialHomeomorph (TotalSpace π A hBranch) (Space m × ℂ) :=
  (toProduct π A hBranch).transOpenPartialHomeomorph (rawChart π A i.point)

theorem chart_center (i : TotalSpace π A hBranch) : i ∈ (chart π A hBranch i).source :=
  rawChart_center π A hBranch i.point

theorem transition_contDiffOn (i j : TotalSpace π A hBranch) :
    ContDiffOn ℂ ω ((chart π A hBranch i).symm.trans (chart π A hBranch j))
      ((chart π A hBranch i).symm.trans (chart π A hBranch j)).source := by
  change ContDiffOn ℂ ω ((rawChart π A i.point).symm.trans (rawChart π A j.point))
    ((rawChart π A i.point).symm.trans (rawChart π A j.point)).source
  exact rawChart_transition_contDiffOn π A i.point j.point

@[instance_reducible] def chartedSpace : ChartedSpace (Space m × ℂ) (TotalSpace π A hBranch) where
  atlas := range (chart π A hBranch)
  chartAt := chart π A hBranch
  mem_chart_source := chart_center π A hBranch
  chart_mem_atlas i := ⟨i, rfl⟩

theorem isComplexManifold : letI := chartedSpace π A hBranch
    IsManifold 𝓘(ℂ, Space m × ℂ) ω (TotalSpace π A hBranch) := by
  let := chartedSpace π A hBranch
  let : HasGroupoid (TotalSpace π A hBranch) (contDiffGroupoid ω 𝓘(ℂ, Space m × ℂ)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ω 𝓘(ℂ, Space m × ℂ))
    intro e f he hf
    change e ∈ range (chart π A hBranch) at he
    change f ∈ range (chart π A hBranch) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    simpa only [contDiffPregroupoid, mfld_simps] using transition_contDiffOn π A hBranch i j
  exact IsManifold.mk' 𝓘(ℂ, Space m × ℂ) ω (TotalSpace π A hBranch)

attribute [instance] chartedSpace isComplexManifold

def projection (p : TotalSpace π A hBranch) : Parameters m := p.point.1

theorem proper_projection : IsProperMap (projection π A hBranch) :=
  isProperMap_fst_of_compactSpace.comp (toProduct π A hBranch).isProperMap

def ambientParameter (p : TotalSpace π A hBranch) : Space m := p.point.1.val

theorem chart_parameter (i p : TotalSpace π A hBranch) :
    (chart π A hBranch i p).1 = ambientParameter π A hBranch p := rawChart_parameter π A i.point p.point

theorem ambientParameter_holomorphic :
    ContMDiff 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) ω (ambientParameter π A hBranch) := by
  intro i
  have hc : ContMDiffAt 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m × ℂ) ω (chart π A hBranch i) i :=
    (contMDiffOn_chart (I := 𝓘(ℂ, Space m × ℂ)) (x := i)).contMDiffAt
      ((chart π A hBranch i).open_source.mem_nhds (chart_center π A hBranch i))
  have hfst : ContMDiff 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) ω (Prod.fst : Space m × ℂ → Space m) :=
    contDiff_fst.contMDiff
  apply ((hfst _).comp i hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun p => (chart_parameter π A hBranch i p).symm

theorem projection_holomorphic :
    ContMDiff 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ, Space m) ω (projection π A hBranch) := by
  intro i
  have hp : ambientParameter π A hBranch i ∈ (ComplexDisplacementParameters.chart m).target := by
    rw [ComplexDisplacementParameters.chart_target]
    exact i.point.1.property
  have hInv : ContMDiffAt 𝓘(ℂ, Space m) 𝓘(ℂ, Space m) ω
      (ComplexDisplacementParameters.chart m).symm (ambientParameter π A hBranch i) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (projection π A hBranch i)) hp
  apply (hInv.comp i (ambientParameter_holomorphic π A hBranch i)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun p => ((ComplexDisplacementParameters.chart m).left_inv
    (show projection π A hBranch p ∈ (ComplexDisplacementParameters.chart m).source by
      rw [ComplexDisplacementParameters.chart_source]; exact mem_univ _)).symm

end VeechDichotomy.NativeAnalyticCoverTotalSpace
