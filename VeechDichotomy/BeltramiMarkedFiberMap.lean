module

public import VeechDichotomy.BeltramiMarkedFiberSurface
public import VeechDichotomy.BeltramiMarkedCoverFiniteMap
public import VeechDichotomy.NativeBeltramiFibers

/-! The literal finite covering map from each constructed native fiber
to its actual native Beltrami base curve. Holomorphicity is derived from
the joint total map and the actual preferred native base charts. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFiberMap

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedFiberSurface
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
  (a : ComplexBeltramiMarkParameters.Parameters A)

def map (y : Surface π F hBranch a) : NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A a) :=
  ⟨BeltramiMarkedBaseTransport.transported F a (π.map y.point)⟩

theorem continuous_map : Continuous (map π F hBranch a) :=
  (NativeBeltramiSurface.toOriginal qX (BeltramiMarkedReferenceCharts.parameter A a)).symm.continuous.comp
    ((BeltramiMarkedBaseTransport.transported F a).continuous.comp
      (π.holomorphic.continuous.comp (toOriginal π F hBranch a).continuous))

theorem total_map (y : Surface π F hBranch a) :
    BeltramiMarkedReferenceSpace.realization A qX
      (BeltramiMarkedCoverTotalSpace.map π F hBranch (inclusion π F hBranch a y)) =
      NativeBeltramiFibers.inclusion qX (BeltramiMarkedReferenceCharts.parameter A a) (map π F hBranch a y) := rfl

theorem holomorphic_map : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (map π F hBranch a) := by
  intro y
  let μ := BeltramiMarkedReferenceCharts.parameter A a
  let r := fun w : Surface π F hBranch a => BeltramiMarkedReferenceSpace.realization A qX
    (BeltramiMarkedCoverTotalSpace.map π F hBranch (inclusion π F hBranch a w))
  have hr : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) ω r y :=
    (BeltramiMarkedReferenceSpace.realization_holomorphic A qX _).comp y
      ((BeltramiMarkedCoverTotalSpace.holomorphic_map π F hBranch _).comp y (holomorphic_inclusion π F hBranch a y))
  let c := NativeBeltramiTotalSpace.chart qX ⟨(μ, (map π F hBranch a y).point)⟩
  have hc : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω c (r y) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (⟨(μ, (map π F hBranch a y).point)⟩ : NativeBeltramiTotalSpace.TotalSpace qX))
      ((NativeBeltramiCharts.chart_source qX (map π F hBranch a y).point _).mpr
        (NativePowerCharts.chosen qX (map π F hBranch a y).point).center)
  have hcoords := hc.comp y hr
  have hs := (contDiff_snd.contMDiff _).comp y hcoords
  rw [contMDiffAt_iff_target_of_mem_source (y := map π F hBranch a y)
    (mem_chart_source ℂ (map π F hBranch a y))]
  exact ⟨(continuous_map π F hBranch a).continuousAt, hs⟩

theorem surjective_map : Function.Surjective (map π F hBranch a) := by
  intro x
  obtain ⟨y, hy⟩ := π.surjective ((BeltramiMarkedBaseTransport.transported F a).symm x.point)
  refine ⟨⟨y⟩, ?_⟩
  apply (NativeBeltramiSurface.toOriginal qX (BeltramiMarkedReferenceCharts.parameter A a)).injective
  change BeltramiMarkedBaseTransport.transported F a (π.map y) = x.point
  rw [hy]
  exact (BeltramiMarkedBaseTransport.transported F a).apply_symm_apply x.point

theorem finite_fibers (x : NativeBeltramiSurface.Surface qX (BeltramiMarkedReferenceCharts.parameter A a)) :
    (map π F hBranch a ⁻¹' {x}).Finite := by
  let H := BeltramiMarkedBaseTransport.transported F a
  apply ((π.finite_fibers (H.symm x.point)).image (toOriginal π F hBranch a).symm).subset
  intro y hy
  have hv := congrArg NativeBeltramiSurface.Surface.point hy
  change H (π.map y.point) = x.point at hv
  have hp : π.map y.point = H.symm x.point := H.injective (hv.trans (H.apply_symm_apply x.point).symm)
  exact ⟨y.point, hp, rfl⟩

def toBeltramiSource : Surface π F hBranch a ≃ₜ NativeBeltramiSurface.Surface qY (BeltramiMarkedReferenceCharts.parameter A a) :=
  (toOriginal π F hBranch a).trans (NativeBeltramiSurface.toOriginal qY (BeltramiMarkedReferenceCharts.parameter A a)).symm

theorem map_factorization (y : Surface π F hBranch a) :
    map π F hBranch a y = F.nativeMap (ComplexBeltramiMarkParameters.productHomeomorph A a)
      ((NativeBeltramiCover.cover π (BeltramiMarkedReferenceCharts.parameter A a)).map (toBeltramiSource π F hBranch a y)) := rfl

end VeechDichotomy.BeltramiMarkedFiberMap
