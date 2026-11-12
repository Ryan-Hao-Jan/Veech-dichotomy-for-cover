module

public import VeechDichotomy.BeltramiMarkedPowerPrimitives

/-! The actual fiber power primitives are restrictions of a jointly
continuous function on an actual open part of the constructed total
space, including zeros and ramification. This supplies common bounds
from compact total neighborhoods, independently of primitive injectivity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedTotalPrimitives

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def baseMap (t : Total π F hBranch) : NativeBeltramiTotalSpace.TotalSpace qX :=
  BeltramiMarkedReferenceSpace.realization A qX (BeltramiMarkedCoverTotalSpace.map π F hBranch t.2)

theorem baseMap_continuous : Continuous (baseMap π F hBranch) :=
  ((BeltramiMarkedReferenceSpace.realization_holomorphic A qX).continuous.comp
    (BeltramiMarkedCoverTotalSpace.holomorphic_map π F hBranch).continuous).comp continuous_snd

def domain (j : X) : Set (Total π F hBranch) :=
  baseMap π F hBranch ⁻¹' (NativeBeltramiTotalSpace.chart qX ⟨(μ₀, j)⟩).source

theorem domain_open (j : X) : IsOpen (domain π F hBranch j) :=
  (NativeBeltramiTotalSpace.chart qX ⟨(μ₀, j)⟩).open_source.preimage (baseMap_continuous π F hBranch)

def primitive (j : X) (t : Total π F hBranch) : ℂ :=
  t.1.val * (NativeBeltramiTotalSpace.chart qX ⟨(μ₀, j)⟩ (baseMap π F hBranch t)).2 ^
    (NativePowerCharts.chosen qX j).exponent

theorem continuousOn_primitive (j : X) : ContinuousOn (primitive π F hBranch j) (domain π F hBranch j) := by
  have hc := (NativeBeltramiTotalSpace.chart qX ⟨(μ₀, j)⟩).continuousOn.comp
    (baseMap_continuous π F hBranch).continuousOn (fun _ ht => ht)
  exact (continuous_subtype_val.comp continuous_fst).continuousOn.mul (hc.snd.pow _)

theorem primitive_inclusion (j : X) (p : Base A) (y : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :
    primitive π F hBranch j (inclusion π F hBranch p y) =
      BeltramiMarkedPowerPrimitives.primitive π F hBranch j p y := rfl

theorem domain_inclusion (j : X) (p : Base A) (y : BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :
    inclusion π F hBranch p y ∈ domain π F hBranch j ↔ y ∈ BeltramiMarkedPowerPrimitives.domain π F hBranch j p := by
  change (BeltramiMarkedReferenceCharts.parameter A p.2, (BeltramiMarkedFiberMap.map π F hBranch p.2 y).point) ∈
    (NativeBeltramiCharts.chart qX j).source ↔
    BeltramiMarkedFiberMap.map π F hBranch p.2 y ∈
      (NativeBeltramiSurface.chart qX (BeltramiMarkedReferenceCharts.parameter A p.2) ⟨j⟩).source
  rw [NativeBeltramiCharts.chart_source, NativeBeltramiSurface.chart_source]

end VeechDichotomy.BeltramiMarkedTotalPrimitives
