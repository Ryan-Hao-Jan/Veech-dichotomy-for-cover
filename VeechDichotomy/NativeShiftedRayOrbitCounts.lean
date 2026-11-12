module

public import VeechDichotomy.NativeRayOrbitComparison

/-! A common target height interval pulls back to actual source orbit
windows based at two arbitrary rectangle points. The source windows may
be shifted, have exactly equal lengths, and their intersections with a
fixed embedded transverse arc differ by at most one. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShiftedRayOrbitCounts

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles
open NativeHorizontalSides NativeHorizontalSlices NativeDeformationRegular WholeDeformedAtlas
open LinearGroup Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (q : Differential X) (v : Plane) (hv : v ≠ 0) (t : ℝ) (r : Differential Y)

local instance : ChartedSpace ℂ (WholeSurface q (NativeTeichmullerRay.matrix v hv t)) :=
  WholeDeformedAtlas.chartedSpace q (NativeTeichmullerRay.matrix v hv t)
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q (NativeTeichmullerRay.matrix v hv t)) :=
  WholeDeformedAtlas.isComplexManifold q (NativeTeichmullerRay.matrix v hv t) ω

variable (e : MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv t) r)
local notation "H" => NativeSL2ArcTransport.homeomorph q (NativeTeichmullerRay.matrix v hv t) r e

def time (i : Index r) (x : Regular q) (a : ℝ) : ℝ :=
  (a - (chart r i (H x)).2) / NativeTeichmullerRay.contraction v t

theorem interval_length (i : Index r) (x : Regular q) (a b : ℝ) :
    time q v hv t r e i x b - time q v hv t r e i x a =
      (b - a) / NativeTeichmullerRay.contraction v t := by
  unfold time
  ring

theorem count_bounds (i : Index r) (x y z : Regular q) (lo hi a b : ℝ)
    (hI : Icc a b ⊆ domain q (NativeRayRectangleComparison.transverse v hv) z)
    (hinj : InjOn (trajectory q (NativeRayRectangleComparison.transverse v hv) z) (Icc a b))
    {l u bot top c d : ℝ} (hc : c ∈ Ioo l u) (hd : d ∈ Ioo l u) (hcd : c < d)
    (hlo : bot < lo) (hhi : hi < top) (hR : rectangle l u bot top ⊆ (chart r i).target)
    (hx : H x ∈ side r i c bot top) (hy : H y ∈ side r i d bot top) :
    (trajectory q v x '' Icc (time q v hv t r e i x lo) (time q v hv t r e i x hi) ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard ≤
      (trajectory q v y '' Icc (time q v hv t r e i y lo) (time q v hv t r e i y hi) ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard + 1 ∧
    (trajectory q v y '' Icc (time q v hv t r e i y lo) (time q v hv t r e i y hi) ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard ≤
      (trajectory q v x '' Icc (time q v hv t r e i x lo) (time q v hv t r e i x hi) ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard + 1 := by
  have hJ : Icc lo hi ⊆ Ioo bot top := fun s hs => ⟨hlo.trans_le hs.1, hs.2.trans_lt hhi⟩
  have hcounts := NativeRayRectangleComparison.rectangle_count_bounds q v hv t r e i z a b hI hinj hc hd hcd hR hJ
  dsimp only [NativeSL2RectangleComparison.sourceCrossings] at hcounts
  rw [NativeRayOrbitComparison.preimage_side q v hv t r e i x lo hi hc hlo hhi hR hx,
    NativeRayOrbitComparison.preimage_side q v hv t r e i y lo hi hd hlo hhi hR hy] at hcounts
  exact hcounts

end VeechDichotomy.NativeShiftedRayOrbitCounts
