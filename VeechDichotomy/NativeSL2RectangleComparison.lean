module

public import VeechDichotomy.NativeSL2ArcTransport
public import VeechDichotomy.NativePrimitiveSimpleArcs

/-! Opposite-side intersection comparison pulled back to the ORIGINAL
native surface through the actual SL2/native-equivalence map. The
expanded horizontal arc, its lifetime and its embedding are derived
from the original native arc. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeSL2RectangleComparison

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles NativeHorizontalSlices
open NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem count_preimage_inter {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]
    (H : U ≃ₜ V) (S : Set V) (T : Set U) : (H ⁻¹' S ∩ T).ncard = (S ∩ H '' T).ncard := by
  have hcard : (H '' (H ⁻¹' S ∩ T)).ncard = (H ⁻¹' S ∩ T).ncard := H.injective.injOn.ncard_image
  rw [← hcard, image_inter H.injective, image_preimage_eq _ H.surjective]

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (q : Differential X) (A : SL2) (r : Differential Y)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

variable (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q A) r)

def sourceCrossings (i : Index r) (v : Plane) (x : Regular q) (c : ℝ) (J : Set ℝ) (a z : ℝ) : Set (Regular q) :=
  NativeSL2ArcTransport.homeomorph q A r e ⁻¹' slice r i c J ∩ trajectory q v x '' Icc a z

theorem source_count_eq (i : Index r) {v : Plane} {k : ℝ} (hk : 0 < k)
    (hvel : planeEquiv A v = k • horizontal) (x : Regular q) (c : ℝ) (J : Set ℝ) (a z : ℝ)
    (hI : Icc a z ⊆ domain q v x) :
    (sourceCrossings q A r e i v x c J a z).ncard =
      NativeRectangleCrossings.crossingCount r i (NativeSL2ArcTransport.homeomorph q A r e x) c J (a * k) (z * k) := by
  unfold sourceCrossings
  rw [count_preimage_inter, NativeSL2ArcTransport.image_arc q A r e hk hvel x a z hI]
  rfl

theorem source_finite (i : Index r) {v : Plane} {k : ℝ} (hk : 0 < k)
    (hvel : planeEquiv A v = k • horizontal) (x : Regular q) (a z : ℝ)
    (hI : Icc a z ⊆ domain q v x) {l u b t c : ℝ} (hc : c ∈ Ioo l u)
    (hR : rectangle l u b t ⊆ (chart r i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b t) :
    (sourceCrossings q A r e i v x c J a z).Finite := by
  let H := NativeSL2ArcTransport.homeomorph q A r e
  have hfin := NativeRectangleCrossings.finite_crossings r i hc hR hJ (H x) (a * k) (z * k)
    (NativeSL2ArcTransport.scaled_interval_domain q A r e hk hvel x a z hI)
  apply (hfin.image H.symm).subset
  intro y hy
  refine ⟨H y, ⟨hy.1, ?_⟩, H.symm_apply_apply y⟩
  have hmem : H y ∈ H '' (trajectory q v x '' Icc a z) := ⟨y, hy.2, rfl⟩
  rwa [NativeSL2ArcTransport.image_arc q A r e hk hvel x a z hI] at hmem

theorem count_bounds (i : Index r) {v : Plane} {k : ℝ} (hk : 0 < k)
    (hvel : planeEquiv A v = k • horizontal) (x : Regular q) (a z : ℝ)
    (hI : Icc a z ⊆ domain q v x) (hinj : InjOn (trajectory q v x) (Icc a z))
    {l u b t c d : ℝ} (hc : c ∈ Ioo l u) (hd : d ∈ Ioo l u) (hcd : c < d)
    (hR : rectangle l u b t ⊆ (chart r i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b t) :
    (sourceCrossings q A r e i v x c J a z).ncard ≤ (sourceCrossings q A r e i v x d J a z).ncard + 1 ∧
      (sourceCrossings q A r e i v x d J a z).ncard ≤ (sourceCrossings q A r e i v x c J a z).ncard + 1 := by
  rw [source_count_eq q A r e i hk hvel x c J a z hI, source_count_eq q A r e i hk hvel x d J a z hI]
  exact NativeRectangleCrossings.count_bounds r i hc hd hcd hR hJ (NativeSL2ArcTransport.homeomorph q A r e x) _ _
    (NativeSL2ArcTransport.scaled_interval_domain q A r e hk hvel x a z hI)
    (NativeSL2ArcTransport.arc_injOn q A r e hk hvel x a z hI hinj)

end VeechDichotomy.NativeSL2RectangleComparison
