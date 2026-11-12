module

public import VeechDichotomy.NativeBeltramiTransitions
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Maps.Proper.Basic

/-! A constructed proper holomorphic deformation family over the complex
unit disk, with the original parameter/surface product topology. The
parameter projection is a submersion, including above differential zeros. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiTotalSpace

open MNEC.NativeAbelianDifferential BeltramiPlane NativeBeltramiTransitions Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

structure TotalSpace (q : Differential X) where
  point : Parameter × X

variable (q : Differential X)

instance topology : TopologicalSpace (TotalSpace q) := TopologicalSpace.induced TotalSpace.point inferInstance

def toProduct : TotalSpace q ≃ₜ Parameter × X where
  toFun := TotalSpace.point
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance t2Space : T2Space (TotalSpace q) := (toProduct q).isEmbedding.t2Space

def chart (i : TotalSpace q) : OpenPartialHomeomorph (TotalSpace q) (ℂ × ℂ) :=
  (toProduct q).transOpenPartialHomeomorph (NativeBeltramiCharts.chart q i.point.2)

theorem chart_center (i : TotalSpace q) : i ∈ (chart q i).source :=
  NativeBeltramiCharts.chart_center q i.point.2 i.point.1

theorem transition_contDiffOn (i j : TotalSpace q) :
    ContDiffOn ℂ ω ((chart q i).symm.trans (chart q j)) ((chart q i).symm.trans (chart q j)).source := by
  change ContDiffOn ℂ ω ((NativeBeltramiCharts.chart q i.point.2).symm.trans (NativeBeltramiCharts.chart q j.point.2))
    ((NativeBeltramiCharts.chart q i.point.2).symm.trans (NativeBeltramiCharts.chart q j.point.2)).source
  exact NativeBeltramiTransitions.transition_contDiffOn q i.point.2 j.point.2

@[instance_reducible] def chartedSpace : ChartedSpace (ℂ × ℂ) (TotalSpace q) where
  atlas := range (chart q)
  chartAt := chart q
  mem_chart_source := chart_center q
  chart_mem_atlas p := ⟨p, rfl⟩

theorem isComplexManifold : letI := chartedSpace q
    IsManifold 𝓘(ℂ, ℂ × ℂ) ω (TotalSpace q) := by
  let := chartedSpace q
  let : HasGroupoid (TotalSpace q) (contDiffGroupoid ω 𝓘(ℂ, ℂ × ℂ)) := by
    apply hasGroupoid_of_pregroupoid (contDiffPregroupoid ω 𝓘(ℂ, ℂ × ℂ))
    intro e f he hf
    change e ∈ range (chart q) at he
    change f ∈ range (chart q) at hf
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := hf
    simpa only [contDiffPregroupoid, mfld_simps] using transition_contDiffOn q i j
  exact IsManifold.mk' 𝓘(ℂ, ℂ × ℂ) ω (TotalSpace q)

attribute [instance] chartedSpace isComplexManifold

def projection (p : TotalSpace q) : Parameter := p.point.1
def ambientParameter (p : TotalSpace q) : ℂ := p.point.1.val

theorem proper_projection : IsProperMap (projection q) :=
  isProperMap_fst_of_compactSpace.comp (toProduct q).isProperMap

theorem chart_parameter (i p : TotalSpace q) : (chart q i p).1 = ambientParameter q p := rfl

theorem ambientParameter_holomorphic : ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω (ambientParameter q) := by
  intro p
  have hc : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (chart q p) p :=
    (contMDiffOn_chart (I := 𝓘(ℂ, ℂ × ℂ)) (x := p)).contMDiffAt ((chart q p).open_source.mem_nhds (chart_center q p))
  have hf : ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω (Prod.fst : ℂ × ℂ → ℂ) := contDiff_fst.contMDiff
  exact (hf _).comp p hc

theorem projection_holomorphic : ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) ω (projection q) := by
  intro p
  have ht : ambientParameter q p ∈ BeltramiParameter.chart.target := by
    rw [BeltramiParameter.chart_target]
    exact p.point.1.property
  have hInv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω BeltramiParameter.chart.symm (ambientParameter q p) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (projection q p)) ht
  apply (hInv.comp p (ambientParameter_holomorphic q p)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun z => (BeltramiParameter.chart.left_inv (mem_univ (projection q z))).symm

theorem ambientParameter_surjective_derivative (p : TotalSpace q) :
    Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (ambientParameter q) p) := by
  have hc : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (chart q p) p :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ, ℂ × ℂ)) (chart_mem_atlas (ℂ × ℂ) p) (mem_chart_source (ℂ × ℂ) p)
  have hf : HasMFDerivAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (Prod.fst : ℂ × ℂ → ℂ) (chart q p p)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) := (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.hasMFDerivAt
  have hd : HasMFDerivAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (ambientParameter q) p
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (chart q p) p)) :=
    hf.comp p hc.hasMFDerivAt
  have hsurj := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ℂ × ℂ))
    (chart_mem_atlas (ℂ × ℂ) p)).mfderiv_surjective (mem_chart_source (ℂ × ℂ) p)
  rw [hd.mfderiv]
  intro v
  obtain ⟨u, hu⟩ := hsurj (v, 0)
  exact ⟨u, congrArg Prod.fst hu⟩

theorem projection_surjective_derivative (p : TotalSpace q) :
    Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (projection q) p) := by
  have hπ : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (projection q) p := (projection_holomorphic q).mdifferentiableAt (by decide)
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) BeltramiParameter.chart (projection q p) :=
    mdifferentiableAt_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (projection q p)) (mem_chart_source ℂ (projection q p))
  have hder : mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (ambientParameter q) p =
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) BeltramiParameter.chart (projection q p)).comp
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (projection q) p) := (hc.hasMFDerivAt.comp p hπ.hasMFDerivAt).mfderiv
  have hinj := (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ))
    (chart_mem_atlas ℂ (projection q p))).mfderiv_injective (mem_chart_source ℂ (projection q p))
  intro v
  obtain ⟨u, hu⟩ := ambientParameter_surjective_derivative q p (mfderiv 𝓘(ℂ) 𝓘(ℂ) BeltramiParameter.chart (projection q p) v)
  refine ⟨u, hinj ?_⟩
  rw [hder] at hu
  exact hu

end VeechDichotomy.NativeBeltramiTotalSpace
