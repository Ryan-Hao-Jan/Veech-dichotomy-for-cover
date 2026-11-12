module

public import VeechDichotomy.NativeFlowboxRayCounts
public import VeechDichotomy.BeltramiMarkedShiftedClocks

/-! Concrete flowbox crossing comparisons along actual returning native
unit-vertical rays. Nearby charts, rectangles and horizontal order are
derived from actual family-point convergence. A fixed common target
height interval yields shifted source crossing windows with count error one. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedFlowboxRayCounts

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativePrimitiveAreaCharts
open NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativeDeformationRegular WholeDeformedAtlas LinearGroup
open BeltramiMarkedRayOrbitCounts BeltramiMarkedShiftedClocks
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
    (x y : CompleteOrbits q vertical) (lo hi : ℝ) (hlo : bot < lo) (hhi : hi < top)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (point π F hBranch q vertical hv t p e x.val n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ x₀)))
    (hy : Tendsto (fun n => inclusion π F hBranch (p n) (point π F hBranch q vertical hv t p e y.val n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ y₀))) :
    ∀ᶠ n in atTop,
      SeparatedWindowCounts.count (D.closedHits x) (τ s x.val lo n) (τ s x.val hi n) ≤
        SeparatedWindowCounts.count (D.closedHits y) (τ s y.val lo n) (τ s y.val hi n) + 1 ∧
      SeparatedWindowCounts.count (D.closedHits y) (τ s y.val lo n) (τ s y.val hi n) ≤
        SeparatedWindowCounts.count (D.closedHits x) (τ s x.val lo n) (τ s x.val hi n) + 1 := by
  have hvertices := BeltramiMarkedRectangleVertices.eventual_vertices π F hBranch s hs hreg p₀ x₀ y₀ hx₀ hy₀
    hR hxR hyR hhor p (point π F hBranch q vertical hv t p e x.val) (point π F hBranch q vertical hv t p e y.val) hx hy
  filter_upwards [hvertices] with n hn
  obtain ⟨i, hfun, hxn, hyn, hRn, hxr, hyr, horder⟩ := hn
  have hxs : point π F hBranch q vertical hv t p e x.val n ∈ NativeHorizontalSides.side (fiberForm π F hBranch (p n)) i
      (chart (fiberForm π F hBranch (p n)) i (point π F hBranch q vertical hv t p e x.val n)).1 bot top :=
    ⟨hxn, rfl, hxr.2⟩
  have hys : point π F hBranch q vertical hv t p e y.val n ∈ NativeHorizontalSides.side (fiberForm π F hBranch (p n)) i
      (chart (fiberForm π F hBranch (p n)) i (point π F hBranch q vertical hv t p e y.val n)).1 bot top :=
    ⟨hyn, rfl, hyr.2⟩
  have hcounts := NativeFlowboxRayCounts.count_bounds q hv (t n) (fiberForm π F hBranch (p n)) (e n) D hmin i x y lo hi
    hxr.1 hyr.1 horder hlo hhi hRn hxs hys
  have htime (z : Regular q) (a : ℝ) :
      NativeShiftedRayOrbitCounts.time q vertical hv (t n) (fiberForm π F hBranch (p n)) (e n) i z a = τ s z a n := by
    change (a - (chart (fiberForm π F hBranch (p n)) i (point π F hBranch q vertical hv t p e z n)).2) /
      NativeTeichmullerRay.contraction vertical (t n) = _
    rw [hfun]
    rfl
  simpa only [htime] using hcounts

end VeechDichotomy.BeltramiMarkedFlowboxRayCounts
