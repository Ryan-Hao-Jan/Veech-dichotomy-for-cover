module

public import VeechDichotomy.NativeFlowboxIntersectionCounts
public import VeechDichotomy.NativeShiftedRayOrbitCounts
public import VeechDichotomy.NativeVerticalRayNormalization

/-! The actual shifted ray rectangle comparison applied to a concrete
source flowbox base. Minimal complete orbit injectivity identifies its
geometric intersections with the actual closed-base crossing counts. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFlowboxRayCounts

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeHorizontalSides NativeBufferedFlowboxes
open NativeDeformationRegular WholeDeformedAtlas LinearGroup Set Filter Topology
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
    (i : Index r) (x y : CompleteOrbits q vertical) (lo hi : ℝ)
    {l u bot top c d : ℝ} (hc : c ∈ Ioo l u) (hd : d ∈ Ioo l u) (hcd : c < d)
    (hlo : bot < lo) (hhi : hi < top) (hR : rectangle l u bot top ⊆ (chart r i).target)
    (hx : H x.val ∈ side r i c bot top) (hy : H y.val ∈ side r i d bot top) :
    SeparatedWindowCounts.count (D.closedHits x) (τ i x.val lo) (τ i x.val hi) ≤
      SeparatedWindowCounts.count (D.closedHits y) (τ i y.val lo) (τ i y.val hi) + 1 ∧
    SeparatedWindowCounts.count (D.closedHits y) (τ i y.val lo) (τ i y.val hi) ≤
      SeparatedWindowCounts.count (D.closedHits x) (τ i x.val lo) (τ i x.val hi) + 1 := by
  have hI : Icc 0 (D.right - D.left) ⊆
      domain q (NativeRayRectangleComparison.transverse vertical hv) D.basePoint := by
    rw [NativeVerticalRayNormalization.transverse_vertical]
    exact D.base_interval_domain
  have hinj : InjOn (trajectory q (NativeRayRectangleComparison.transverse vertical hv) D.basePoint)
      (Icc 0 (D.right - D.left)) := by
    rw [NativeVerticalRayNormalization.transverse_vertical]
    exact D.base_arc_injective
  have hbnd := NativeShiftedRayOrbitCounts.count_bounds q vertical hv t r e i x.val y.val D.basePoint
    lo hi 0 (D.right - D.left) hI hinj hc hd hcd hlo hhi hR hx hy
  simpa only [NativeVerticalRayNormalization.transverse_vertical,
    D.base_intersection_count hmin x, D.base_intersection_count hmin y] using hbnd

end VeechDichotomy.NativeFlowboxRayCounts
