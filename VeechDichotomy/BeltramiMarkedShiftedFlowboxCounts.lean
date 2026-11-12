module

public import VeechDichotomy.BeltramiMarkedShiftedSourcePoints
public import VeechDichotomy.NativeShiftedFlowboxRayCounts

/-! Actual returning-family rectangle comparisons for vertices moving
along complete source orbits. The count windows are translated back to
the ORIGINAL fixed source points, whose statistical profiles are known. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedShiftedFlowboxCounts

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativePrimitiveAreaCharts
open NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativeDeformationRegular WholeDeformedAtlas LinearGroup
open BeltramiMarkedShiftedSourcePoints
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (hv : vertical ≠ (0 : Plane)) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q vertical hv (t n)) (fiberForm π F hBranch (p n)))
local notation "τ" => time π F hBranch q vertical hv t p e
local notation "P" => point π F hBranch q vertical hv t p e

theorem comparison (D : NativeBufferedFlowboxes.Data q) (hmin : NativeDynamics.MinimalDirection q vertical)
    (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (hs : s.2 ∉ criticalSet π) (hreg : BeltramiMarkedRegularSlices.baseCenter π F s ∈ regularSet qX)
    (p₀ : Base A) (x₀ y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (hy₀ : y₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    {l r bot top : ℝ}
    (hR : ∀ a ∈ Icc l r ×ˢ Icc bot top, toPlane.symm a ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (hxR : coordinate π F hBranch s (inclusion π F hBranch p₀ x₀) ∈ rectangle l r bot top)
    (hyR : coordinate π F hBranch s (inclusion π F hBranch p₀ y₀) ∈ rectangle l r bot top)
    (hhor : (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).1 <
      (coordinate π F hBranch s (inclusion π F hBranch p₀ y₀)).1)
    (x y : CompleteOrbits q vertical) (dx dy : ℕ → ℝ) (lo hi : ℝ) (hlo : bot < lo) (hhi : hi < top)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (P x dx n).val) atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (P y dy n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀))) :
    ∀ᶠ n in atTop,
      SeparatedWindowCounts.count (D.closedHits x) (τ s x dx lo n) (τ s x dx hi n) ≤
        SeparatedWindowCounts.count (D.closedHits y) (τ s y dy lo n) (τ s y dy hi n) + 1 ∧
      SeparatedWindowCounts.count (D.closedHits y) (τ s y dy lo n) (τ s y dy hi n) ≤
        SeparatedWindowCounts.count (D.closedHits x) (τ s x dx lo n) (τ s x dx hi n) + 1 := by
  have hvertices := BeltramiMarkedRectangleVertices.eventual_vertices π F hBranch s hs hreg p₀ x₀ y₀ hx₀ hy₀
    hR hxR hyR hhor p (P x dx) (P y dy) hx hy
  filter_upwards [hvertices] with n hn
  obtain ⟨i, hfun, hxn, hyn, hRn, hxr, hyr, horder⟩ := hn
  have hxs : P x dx n ∈ NativeHorizontalSides.side (fiberForm π F hBranch (p n)) i
      (chart (fiberForm π F hBranch (p n)) i (P x dx n)).1 bot top := ⟨hxn, rfl, hxr.2⟩
  have hys : P y dy n ∈ NativeHorizontalSides.side (fiberForm π F hBranch (p n)) i
      (chart (fiberForm π F hBranch (p n)) i (P y dy n)).1 bot top := ⟨hyn, rfl, hyr.2⟩
  have hcounts := NativeShiftedFlowboxRayCounts.count_bounds q hv (t n) (fiberForm π F hBranch (p n)) (e n) D hmin i x y
    (dx n / NativeTeichmullerRay.contraction vertical (t n)) (dy n / NativeTeichmullerRay.contraction vertical (t n))
    lo hi hxr.1 hyr.1 horder hlo hhi hRn hxs hys
  have htime (z : CompleteOrbits q vertical) (a : ℕ → ℝ) (h : ℝ) :=
    native_time π F hBranch q vertical hv t p e s n i z a h hfun
  dsimp only [sourcePhase] at htime
  simpa only [htime] using hcounts

end VeechDichotomy.BeltramiMarkedShiftedFlowboxCounts
