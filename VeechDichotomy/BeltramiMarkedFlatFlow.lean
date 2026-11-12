module

public import VeechDichotomy.NativePrimitiveRectangles
public import VeechDichotomy.BeltramiMarkedFlatArea
public import VeechDichotomy.BeltramiMarkedSliceCoordinates

/-! Actual directional trajectories in the constructed marked native
family are inverse fixed-chart straight lines. This applies on every
fiber, with time bounds depending only on a persistent rectangle. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFlatFlow

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativePrimitiveRectangles
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (s : ComplexBeltramiMarkParameters.Parameters A × Y)
  (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)

include hs hreg in
theorem interval_representation (p : Base A) (z₀ : ℂ)
    (hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target)
    (v : Plane) (x : Regular (fiberForm π F hBranch p))
    (hx : x.val ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).source)
    (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I) (hzero : 0 ∈ I)
    (hline : ∀ t ∈ I, toPlane.symm (coordinate π F hBranch s (inclusion π F hBranch p x.val) + t • v) ∈
      (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    I ⊆ domain (fiberForm π F hBranch p) v x ∧ ∀ t ∈ I,
      inclusion π F hBranch p (trajectory (fiberForm π F hBranch p) v x t).val =
        BeltramiMarkedUniformSlices.inverse π F hBranch s
          (p, toPlane.symm (coordinate π F hBranch s (inclusion π F hBranch p x.val) + t • v)) := by
  let i := BeltramiMarkedFlatArea.index π F hBranch s hs hreg p z₀ hz₀
  have hxi : x ∈ (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch p) i).source := by
    rw [MNEC.NativePrimitiveAreaCharts.chart_source]
    exact hx
  have hli : ∀ t ∈ I, MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch p) i x + t • v ∈
      (MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch p) i).target := by
    intro t ht
    rw [MNEC.NativePrimitiveAreaCharts.chart_target]
    exact hline t ht
  have hrep := NativePrimitiveChartFlow.interval_representation (fiberForm π F hBranch p) i v x hxi I hI hord hzero hli
  refine ⟨hrep.1, fun t ht => ?_⟩
  have hpoint := NativePrimitiveChartFlow.primitive_trajectory (fiberForm π F hBranch p) i v x hxi I hI hord hzero hli ht
  change (trajectory (fiberForm π F hBranch p) v x t).val =
    (BeltramiMarkedScaledSlices.chart π F hBranch s p).symm
      (toPlane.symm (coordinate π F hBranch s (inclusion π F hBranch p x.val) + t • v)) at hpoint
  rw [hpoint]
  exact (BeltramiMarkedUniformSlices.inverse_value π F hBranch s p (hline t ht)).symm

include hs hreg in
theorem uniform_vertical_time (p : Base A) (z₀ : ℂ)
    (hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target)
    {W H : ℝ} (hH : 0 < H)
    (hR : ∀ v ∈ rectangle (-W) W (-H) H, toPlane.symm v ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target)
    (x : Regular (fiberForm π F hBranch p))
    (hx : x.val ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).source)
    (hxr : coordinate π F hBranch s (inclusion π F hBranch p x.val) ∈ rectangle (-W) W (-(H / 2)) (H / 2)) :
    Ioo (-(H / 2)) (H / 2) ⊆ domain (fiberForm π F hBranch p) vertical x ∧
      ∀ t ∈ Ioo (-(H / 2)) (H / 2), inclusion π F hBranch p (trajectory (fiberForm π F hBranch p) vertical x t).val =
        BeltramiMarkedUniformSlices.inverse π F hBranch s
          (p, toPlane.symm (coordinate π F hBranch s (inclusion π F hBranch p x.val) + t • vertical)) := by
  apply interval_representation π F hBranch s hs hreg p z₀ hz₀ vertical x hx _ isOpen_Ioo ordConnected_Ioo
    (by constructor <;> linarith)
  intro t ht
  apply hR
  rw [add_vertical]
  exact ⟨hxr.1, by constructor <;> linarith [hxr.2.1, hxr.2.2, ht.1, ht.2]⟩

end VeechDichotomy.BeltramiMarkedFlatFlow
