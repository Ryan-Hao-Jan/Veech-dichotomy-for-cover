module

public import VeechDichotomy.NativeBufferedFlowboxes
public import Mathlib.Topology.Bases

/-! Actual buffered primitive flowboxes refine every regular-point
neighborhood. This supplies geometric test sets independently of any
chosen invariant measure or statistical subsequence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFlowboxNeighborhoods

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts NativePrimitiveRectangles NativeBufferedFlowboxes Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

theorem exists_box (x : Regular q) {U : Set (Regular q)} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ D : Data q, x ∈ D.region ∧ D.region ⊆ U := by
  obtain ⟨i, hi⟩ := covers q x
  let c := chart q i
  have hV : IsOpen (c.target ∩ c.symm ⁻¹' U) :=
    c.symm.continuousOn.isOpen_inter_preimage c.open_target hU
  have hxV : c x ∈ c.target ∩ c.symm ⁻¹' U :=
    ⟨c.map_source hi, by simpa only [mem_preimage, c.left_inv hi] using hxU⟩
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp (hV.mem_nhds hxV)
  obtain ⟨l0, r0, hlr, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp hP
  obtain ⟨b0, u0, hbu, hJ⟩ := mem_nhds_iff_exists_Ioo_subset.mp hQ
  change (c x).1 ∈ Ioo l0 r0 at hlr
  change (c x).2 ∈ Ioo b0 u0 at hbu
  have hrect : rectangle l0 r0 b0 u0 ⊆ c.target ∩ c.symm ⁻¹' U := by
    intro p hp
    exact hPQ ⟨hI hp.1, hJ hp.2⟩
  let D : Data q := {
    index := i
    left := (l0 + (c x).1) / 2
    right := ((c x).1 + r0) / 2
    bottom := (b0 + (c x).2) / 2
    height := (u0 - b0) / 2
    outerLeft := l0, outerRight := r0, outerBottom := b0, outerTop := u0
    width_pos := by linarith [hlr.1, hlr.2]
    height_pos := by linarith [hbu.1, hbu.2]
    left_buffer := by linarith [hlr.1]
    right_buffer := by linarith [hlr.2]
    bottom_buffer := by linarith [hbu.1]
    top_buffer := by linarith [hbu.2]
    target := fun p hp => (hrect hp).1 }
  refine ⟨D, ?_, ?_⟩
  · refine ⟨hi, ?_⟩
    change c x ∈ rectangle ((l0 + (c x).1) / 2) (((c x).1 + r0) / 2)
      ((b0 + (c x).2) / 2) ((b0 + (c x).2) / 2 + (u0 - b0) / 2)
    exact ⟨⟨by linarith [hlr.1], by linarith [hlr.2]⟩,
      ⟨by linarith [hbu.1], by linarith [hbu.2]⟩⟩
  · intro y hy
    have hp : c y ∈ rectangle l0 r0 b0 u0 := by
      have hxy : (c y).1 ∈ Ioo D.left D.right := hy.2.1
      have hyz : (c y).2 ∈ Ioo D.bottom (D.bottom + D.height) := hy.2.2
      exact ⟨⟨D.left_buffer.trans hxy.1, hxy.2.trans D.right_buffer⟩,
        ⟨D.bottom_buffer.trans hyz.1, hyz.2.trans D.top_buffer⟩⟩
    have hyU := (hrect hp).2
    simpa only [mem_preimage, c.left_inv hy.1] using hyU

end VeechDichotomy.NativeFlowboxNeighborhoods
