module

public import VeechDichotomy.NativeSL2RectangleComparison
public import VeechDichotomy.NativeTeichmullerRay
public import VeechDichotomy.NativeVerticalSlices

/-! The actual contracting Teichmuller ray expands the constructed
transverse direction, contracts the tested direction, and transfers
rectangle crossing bounds to the ORIGINAL native surface. Pulled-back
vertical times diverge for convergent positive rectangle heights. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRayRectangleComparison

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics
open NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

def transverse (v : Plane) (hv : v ≠ 0) : Plane :=
  (planeEquiv (NativeTeichmullerRay.rotationToVertical v hv)).symm NativePrimitiveRectangles.horizontal

theorem transverse_ne_zero (v : Plane) (hv : v ≠ 0) : transverse v hv ≠ 0 := by
  intro h
  have h0 := congrArg (planeEquiv (NativeTeichmullerRay.rotationToVertical v hv)) h
  have hbad : NativePrimitiveRectangles.horizontal = (0 : Plane) := by
    simpa only [transverse, ContinuousLinearEquiv.apply_symm_apply, map_zero] using h0
  have hfirst := congrArg Prod.fst hbad
  simp [NativePrimitiveRectangles.horizontal] at hfirst

theorem expanding_velocity (v : Plane) (hv : v ≠ 0) (t : ℝ) :
    planeEquiv (NativeTeichmullerRay.matrix v hv t) (transverse v hv) =
      Real.exp t • NativePrimitiveRectangles.horizontal := by
  rw [NativeTeichmullerRay.matrix, planeEquiv_mul]
  change planeEquiv (NativeTeichmullerRay.diagonal t)
    (planeEquiv (NativeTeichmullerRay.rotationToVertical v hv)
      ((planeEquiv (NativeTeichmullerRay.rotationToVertical v hv)).symm NativePrimitiveRectangles.horizontal)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, NativeTeichmullerRay.diagonal_velocity]
  apply Prod.ext <;> simp [NativePrimitiveRectangles.horizontal]

theorem lifted_time_tendsto {J : Type*} {l : Filter J} (v : Plane) (hv : v ≠ 0)
    {t H : J → ℝ} {H₀ : ℝ} (ht : Tendsto t l atTop) (hH : Tendsto H l (𝓝 H₀)) (hH₀ : 0 < H₀) :
    Tendsto (fun j => H j / NativeTeichmullerRay.contraction v (t j)) l atTop := by
  have hk : Tendsto (fun j => NativeTeichmullerRay.contraction v (t j)) l (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(NativeTeichmullerRay.contraction_tendsto_zero v).comp ht,
      Eventually.of_forall (fun j => NativeTeichmullerRay.contraction_pos v hv (t j))⟩
  simpa only [div_eq_mul_inv, Pi.inv_apply] using hH.pos_mul_atTop hH₀ hk.inv_tendsto_nhdsGT_zero

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

theorem exists_transverse_segment (i : Index q) (x : Regular q) (hx : x ∈ (chart q i).source) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (-ε) ε ⊆ domain q (transverse v hv) x ∧
      InjOn (trajectory q (transverse v hv) x) (Icc (-ε) ε) :=
  NativePrimitiveSimpleArcs.exists_direction_segment q i (transverse v hv) (transverse_ne_zero v hv) x hx

theorem vertical_lift (x : Regular q) (L : ℝ)
    (hL : L ∈ domain r NativePrimitiveRectangles.vertical
      (NativeSL2ArcTransport.homeomorph q (NativeTeichmullerRay.matrix v hv t) r e x)) :
    L / NativeTeichmullerRay.contraction v t ∈ domain q v x ∧
      NativeSL2ArcTransport.homeomorph q (NativeTeichmullerRay.matrix v hv t) r e
        (trajectory q v x (L / NativeTeichmullerRay.contraction v t)) =
          trajectory r NativePrimitiveRectangles.vertical
            (NativeSL2ArcTransport.homeomorph q (NativeTeichmullerRay.matrix v hv t) r e x) L := by
  have hk := (NativeTeichmullerRay.contraction_pos v hv t).ne'
  have hvel : planeEquiv (NativeTeichmullerRay.matrix v hv t) v =
      NativeTeichmullerRay.contraction v t • NativePrimitiveRectangles.vertical := by
    simpa only [NativeTeichmullerRay.vertical, NativePrimitiveRectangles.vertical] using
      NativeTeichmullerRay.contracted_velocity v hv t
  have hsource : L / NativeTeichmullerRay.contraction v t ∈ domain q v x := by
    rw [NativeSL2ArcTransport.domain_clock q _ r e hk hvel x]
    simpa only [mem_ofPred_eq, div_mul_cancel₀ _ hk] using hL
  refine ⟨hsource, ?_⟩
  simpa only [div_mul_cancel₀ _ hk] using
    NativeSL2ArcTransport.trajectory_clock q _ r e hk hvel x (L / NativeTeichmullerRay.contraction v t) hsource

theorem rectangle_count_bounds (i : Index r) (x : Regular q) (a z : ℝ)
    (hI : Icc a z ⊆ domain q (transverse v hv) x) (hinj : InjOn (trajectory q (transverse v hv) x) (Icc a z))
    {l u b h c d : ℝ} (hc : c ∈ Ioo l u) (hd : d ∈ Ioo l u) (hcd : c < d)
    (hR : NativePrimitiveRectangles.rectangle l u b h ⊆ (chart r i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b h) :
    (NativeSL2RectangleComparison.sourceCrossings q (NativeTeichmullerRay.matrix v hv t) r e i (transverse v hv) x c J a z).ncard ≤
        (NativeSL2RectangleComparison.sourceCrossings q (NativeTeichmullerRay.matrix v hv t) r e i (transverse v hv) x d J a z).ncard + 1 ∧
      (NativeSL2RectangleComparison.sourceCrossings q (NativeTeichmullerRay.matrix v hv t) r e i (transverse v hv) x d J a z).ncard ≤
        (NativeSL2RectangleComparison.sourceCrossings q (NativeTeichmullerRay.matrix v hv t) r e i (transverse v hv) x c J a z).ncard + 1 :=
  NativeSL2RectangleComparison.count_bounds q _ r e i (Real.exp_pos t) (expanding_velocity v hv t) x a z hI hinj hc hd hcd hR hJ

end VeechDichotomy.NativeRayRectangleComparison
