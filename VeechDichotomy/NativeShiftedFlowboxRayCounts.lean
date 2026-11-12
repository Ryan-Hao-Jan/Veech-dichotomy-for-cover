module

public import VeechDichotomy.NativeCompleteOrbitShifts
public import VeechDichotomy.NativeFlowboxRayCounts

/-! Shifted target rectangle vertices may be obtained by translating the
original fixed source points along their actual complete orbits. The
rectangle count comparison then applies to translated crossing windows
of those SAME fixed source points. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShiftedFlowboxRayCounts

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeHorizontalSides NativeBufferedFlowboxes
open NativeDeformationRegular WholeDeformedAtlas LinearGroup Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (q : Differential X) (hv : vertical ≠ (0 : Plane)) (t : ℝ) (r : Differential Y)

local instance : ChartedSpace ℂ (WholeSurface q (NativeTeichmullerRay.matrix vertical hv t)) :=
  WholeDeformedAtlas.chartedSpace q (NativeTeichmullerRay.matrix vertical hv t)
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q (NativeTeichmullerRay.matrix vertical hv t)) :=
  WholeDeformedAtlas.isComplexManifold q (NativeTeichmullerRay.matrix vertical hv t) ω

variable (e : MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q vertical hv t) r)
local notation "H" => NativeSL2ArcTransport.homeomorph q (NativeTeichmullerRay.matrix vertical hv t) r e
local notation "τ" => NativeShiftedRayOrbitCounts.time q vertical hv t r e

theorem count_bounds (D : Data q) (hmin : NativeDynamics.MinimalDirection q vertical)
    (i : Index r) (x y : CompleteOrbits q vertical) (sx sy lo hi : ℝ)
    {l u bot top c d : ℝ} (hc : c ∈ Ioo l u) (hd : d ∈ Ioo l u) (hcd : c < d)
    (hlo : bot < lo) (hhi : hi < top) (hR : rectangle l u bot top ⊆ (chart r i).target)
    (hx : H (timeMap q vertical sx x).val ∈ side r i c bot top)
    (hy : H (timeMap q vertical sy y).val ∈ side r i d bot top) :
    SeparatedWindowCounts.count (D.closedHits x)
      (τ i (timeMap q vertical sx x).val lo + sx) (τ i (timeMap q vertical sx x).val hi + sx) ≤
      SeparatedWindowCounts.count (D.closedHits y)
        (τ i (timeMap q vertical sy y).val lo + sy) (τ i (timeMap q vertical sy y).val hi + sy) + 1 ∧
    SeparatedWindowCounts.count (D.closedHits y)
      (τ i (timeMap q vertical sy y).val lo + sy) (τ i (timeMap q vertical sy y).val hi + sy) ≤
      SeparatedWindowCounts.count (D.closedHits x)
        (τ i (timeMap q vertical sx x).val lo + sx) (τ i (timeMap q vertical sx x).val hi + sx) + 1 := by
  have hbnd := NativeFlowboxRayCounts.count_bounds q hv t r e D hmin i
    (timeMap q vertical sx x) (timeMap q vertical sy y) lo hi hc hd hcd hlo hhi hR hx hy
  simpa only [NativeCompleteOrbitShifts.closed_count_shift] using hbnd

end VeechDichotomy.NativeShiftedFlowboxRayCounts
