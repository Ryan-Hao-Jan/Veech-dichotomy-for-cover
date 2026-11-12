module

public import VeechDichotomy.NativeRayRectangleComparison

/-! The opposite rectangle sides pull back to equal-length actual
source orbit segments, one forward and one backward from the chosen
source points. Their intersections with a fixed embedded transverse
source arc differ by at most one. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRayOrbitComparison

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles NativeHorizontalSides NativeHorizontalSlices
open NativeDeformationRegular WholeDeformedAtlas LinearGroup Set Filter Topology
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

def segmentTime (i : Index r) (x y : Regular q) : ℝ :=
  ((chart r i (H y)).2 - (chart r i (H x)).2) / NativeTeichmullerRay.contraction v t

theorem preimage_side (i : Index r) (x : Regular q) (lo hi : ℝ)
    {l u b h c : ℝ} (hc : c ∈ Ioo l u) (hlo : b < lo) (hhi : hi < h)
    (hR : rectangle l u b h ⊆ (chart r i).target) (hx : H x ∈ side r i c b h) :
    H ⁻¹' slice r i c (Icc lo hi) = trajectory q v x ''
      Icc ((lo - (chart r i (H x)).2) / NativeTeichmullerRay.contraction v t)
        ((hi - (chart r i (H x)).2) / NativeTeichmullerRay.contraction v t) := by
  have hvel : LinearEquivalences.planeEquiv (NativeTeichmullerRay.matrix v hv t) v =
      NativeTeichmullerRay.contraction v t • vertical := by
    simpa only [NativeTeichmullerRay.vertical, vertical] using NativeTeichmullerRay.contracted_velocity v hv t
  rw [NativeVerticalSlices.slice_eq_segment r i hc hlo hhi hR (H x) hx]
  exact NativeSL2ArcTransport.preimage_arc q _ r e (NativeTeichmullerRay.contraction_pos v hv t) hvel x _ _
    (NativeVerticalSlices.segment_domain r i hc hlo hhi hR (H x) hx)

theorem finite_intersections (i : Index r) (x z : Regular q) (lo hi a b : ℝ)
    (hI : Icc a b ⊆ domain q (NativeRayRectangleComparison.transverse v hv) z)
    {l u bot top c : ℝ} (hc : c ∈ Ioo l u) (hlo : bot < lo) (hhi : hi < top)
    (hR : rectangle l u bot top ⊆ (chart r i).target) (hx : H x ∈ side r i c bot top) :
    (trajectory q v x '' Icc
      ((lo - (chart r i (H x)).2) / NativeTeichmullerRay.contraction v t)
      ((hi - (chart r i (H x)).2) / NativeTeichmullerRay.contraction v t) ∩
      trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).Finite := by
  have hJ : Icc lo hi ⊆ Ioo bot top := fun s hs => ⟨hlo.trans_le hs.1, hs.2.trans_lt hhi⟩
  have hfin := NativeSL2RectangleComparison.source_finite q (NativeTeichmullerRay.matrix v hv t) r e i
    (Real.exp_pos t) (NativeRayRectangleComparison.expanding_velocity v hv t) z a b hI hc hR hJ
  dsimp only [NativeSL2RectangleComparison.sourceCrossings] at hfin
  rwa [preimage_side q v hv t r e i x lo hi hc hlo hhi hR hx] at hfin

theorem opposite_orbit_counts (i : Index r) (x y z : Regular q) (a b : ℝ)
    (hI : Icc a b ⊆ domain q (NativeRayRectangleComparison.transverse v hv) z)
    (hinj : InjOn (trajectory q (NativeRayRectangleComparison.transverse v hv) z) (Icc a b))
    {l u bot top c d : ℝ} (hc : c ∈ Ioo l u) (hd : d ∈ Ioo l u) (hcd : c < d)
    (hR : rectangle l u bot top ⊆ (chart r i).target)
    (hx : H x ∈ side r i c bot top) (hy : H y ∈ side r i d bot top) :
    (trajectory q v x '' Icc 0 (segmentTime q v hv t r e i x y) ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard ≤
      (trajectory q v y '' Icc (-(segmentTime q v hv t r e i x y)) 0 ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard + 1 ∧
    (trajectory q v y '' Icc (-(segmentTime q v hv t r e i x y)) 0 ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard ≤
      (trajectory q v x '' Icc 0 (segmentTime q v hv t r e i x y) ∩
        trajectory q (NativeRayRectangleComparison.transverse v hv) z '' Icc a b).ncard + 1 := by
  let J := Icc (chart r i (H x)).2 (chart r i (H y)).2
  have hJ : J ⊆ Ioo bot top := fun s hs => ⟨hx.2.2.1.trans_le hs.1, hs.2.trans_lt hy.2.2.2⟩
  have hleft : H ⁻¹' slice r i c J = trajectory q v x '' Icc 0 (segmentTime q v hv t r e i x y) := by
    simpa only [J, sub_self, zero_div, segmentTime] using
      preimage_side q v hv t r e i x _ _ hc hx.2.2.1 hy.2.2.2 hR hx
  have hright : H ⁻¹' slice r i d J = trajectory q v y '' Icc (-(segmentTime q v hv t r e i x y)) 0 := by
    have hneg : ((chart r i (H x)).2 - (chart r i (H y)).2) / NativeTeichmullerRay.contraction v t =
        -(segmentTime q v hv t r e i x y) := by dsimp only [segmentTime]; ring
    simpa only [J, hneg, sub_self, zero_div] using
      preimage_side q v hv t r e i y _ _ hd hx.2.2.1 hy.2.2.2 hR hy
  have hcounts := NativeRayRectangleComparison.rectangle_count_bounds q v hv t r e i z a b hI hinj hc hd hcd hR hJ
  dsimp only [NativeSL2RectangleComparison.sourceCrossings] at hcounts
  rwa [hleft, hright] at hcounts

end VeechDichotomy.NativeRayOrbitComparison
