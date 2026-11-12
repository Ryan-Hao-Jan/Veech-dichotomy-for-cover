module

public import VeechDichotomy.BeltramiMarkedScaledSlices
public import MNEC.NativeRegularArea

/-! Exact physical-area formulas in the actual persistent flat charts.
The canonical native measure sees every such chart as Lebesgue area;
no assumed area convergence or preferred-primitive compatibility enters. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFlatArea

open MNEC.NativeAbelianDifferential MNEC.LatticeTorus NativeTranslationCover BeltramiPlane Set Filter Topology MeasureTheory
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open MNEC.NativeRegularTranslationAtlas
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def index (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) (z₀ : ℂ) (hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    MNEC.NativePrimitiveAreaCharts.Index (fiberForm π F hBranch p) :=
  ⟨⟨(BeltramiMarkedScaledSlices.chart π F hBranch s p).symm z₀,
      BeltramiMarkedScaledSlices.regular_source π F hBranch s hs hreg p
        ((BeltramiMarkedScaledSlices.chart π F hBranch s p).map_target hz₀)⟩,
    BeltramiMarkedScaledSlices.primitiveChart π F hBranch s hs hreg p _
      ((BeltramiMarkedScaledSlices.chart π F hBranch s p).map_target hz₀)⟩

def chart (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) (z₀ : ℂ) (hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    OpenPartialHomeomorph (MNEC.NativeRegularTranslationAtlas.Regular (fiberForm π F hBranch p)) Plane :=
  MNEC.NativePrimitiveAreaCharts.chart (fiberForm π F hBranch p) (index π F hBranch s hs hreg p z₀ hz₀)

theorem chart_target (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) (z₀ : ℂ) (hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    (chart π F hBranch s hs hreg p z₀ hz₀).target =
      toPlane.symm ⁻¹' (BeltramiMarkedScaledSlices.chart π F hBranch s p).target :=
  MNEC.NativePrimitiveAreaCharts.chart_target _ _

theorem inverse_value (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) (z₀ : ℂ) (hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target)
    (v : Plane) (hv : toPlane.symm v ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    ((chart π F hBranch s hs hreg p z₀ hz₀).symm v).val =
      (BeltramiMarkedScaledSlices.chart π F hBranch s p).symm (toPlane.symm v) :=
  MNEC.NativePrimitiveAreaCharts.chart_symm_value _ _ v
    (by change v ∈ (chart π F hBranch s hs hreg p z₀ hz₀).target
        rw [chart_target]; exact hv)

theorem area_image (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p : Base A) (z₀ : ℂ) (hz₀ : z₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p).target)
    (B : Set Plane) (hB : MeasurableSet B)
    (hsub : B ⊆ toPlane.symm ⁻¹' (BeltramiMarkedScaledSlices.chart π F hBranch s p).target) :
    MNEC.NativeRegularArea.regularArea (fiberForm π F hBranch p)
      ((chart π F hBranch s hs hreg p z₀ hz₀).symm '' B) = volume B := by
  apply MNEC.NativeRegularArea.primitive_chart_image
  · exact hB
  · rwa [MNEC.NativePrimitiveAreaCharts.chart_target]

end VeechDichotomy.BeltramiMarkedFlatArea
