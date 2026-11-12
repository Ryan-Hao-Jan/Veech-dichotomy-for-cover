module

public import VeechDichotomy.NativeBufferedFlowboxes

/-! Every concrete native flowbox base is an actual embedded horizontal
flow segment, with its native lifetime and coordinates proved from the
buffered primitive chart. This connects the statistical transversal to
the arcs used in native deformation/rectangle intersection comparisons. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBufferedFlowboxes.Data

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics
open NativePrimitiveRectangles Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} (D : NativeBufferedFlowboxes.Data q)

def basePoint : Regular q := (chart q D.index).symm (D.left, D.bottom)
def baseSet : Set (Regular q) := NativeClosedBaseHits.closedBase q D.index D.left D.right D.bottom

theorem base_target {s : ℝ} (hs : s ∈ Icc D.left D.right) :
    (s, D.bottom) ∈ (chart q D.index).target := by
  apply D.target
  exact ⟨⟨D.left_buffer.trans_le hs.1, hs.2.trans_lt D.right_buffer⟩,
    ⟨D.bottom_buffer, by linarith [D.height_pos, D.top_buffer]⟩⟩

theorem basePoint_source : D.basePoint ∈ (chart q D.index).source :=
  (chart q D.index).map_target (D.base_target ⟨le_rfl, D.width_pos.le⟩)

theorem basePoint_coordinates : chart q D.index D.basePoint = (D.left, D.bottom) :=
  (chart q D.index).right_inv (D.base_target ⟨le_rfl, D.width_pos.le⟩)

theorem base_segment {t : ℝ} (ht : t ∈ Icc 0 (D.right - D.left)) :
    t ∈ domain q horizontal D.basePoint ∧
      trajectory q horizontal D.basePoint t ∈ (chart q D.index).source ∧
        chart q D.index (trajectory q horizontal D.basePoint t) = (D.left + t, D.bottom) := by
  have hxr : chart q D.index D.basePoint ∈
      rectangle D.outerLeft D.outerRight D.outerBottom D.outerTop := by
    rw [D.basePoint_coordinates]
    exact ⟨⟨D.left_buffer, D.width_pos.trans D.right_buffer⟩,
      ⟨D.bottom_buffer, by linarith [D.height_pos, D.top_buffer]⟩⟩
  have htime : t ∈ Ioo (D.outerLeft - (chart q D.index D.basePoint).1)
      (D.outerRight - (chart q D.index D.basePoint).1) := by
    rw [D.basePoint_coordinates]
    constructor <;> dsimp <;> linarith [ht.1, ht.2, D.left_buffer, D.right_buffer]
  have hseg := horizontal_interval q D.index D.target D.basePoint D.basePoint_source hxr
  have heq : trajectory q horizontal D.basePoint t = (chart q D.index).symm (D.left + t, D.bottom) := by
    simpa only [D.basePoint_coordinates] using hseg.2 t htime
  have hp : (D.left + t, D.bottom) ∈ (chart q D.index).target :=
    D.base_target ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨hseg.1 htime, ?_, ?_⟩
  · rw [heq]
    exact (chart q D.index).map_target hp
  · rw [heq]
    exact (chart q D.index).right_inv hp

theorem base_interval_domain : Icc 0 (D.right - D.left) ⊆ domain q horizontal D.basePoint :=
  fun _ ht => (D.base_segment ht).1

theorem base_arc_injective : InjOn (trajectory q horizontal D.basePoint) (Icc 0 (D.right - D.left)) := by
  intro s hs t ht hst
  have hc := congrArg (fun y => (chart q D.index y).1) hst
  rw [(D.base_segment hs).2.2, (D.base_segment ht).2.2] at hc
  dsimp at hc
  linarith

theorem baseSet_eq_arc : D.baseSet = trajectory q horizontal D.basePoint '' Icc 0 (D.right - D.left) := by
  ext y
  constructor
  · intro hy
    have ht : (chart q D.index y).1 - D.left ∈ Icc 0 (D.right - D.left) := by
      constructor <;> linarith [hy.2.1.1, hy.2.1.2]
    refine ⟨(chart q D.index y).1 - D.left, ht, ?_⟩
    apply (chart q D.index).injOn (D.base_segment ht).2.1 hy.1
    rw [(D.base_segment ht).2.2]
    apply Prod.ext
    · dsimp
      ring
    · exact hy.2.2.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(D.base_segment ht).2.1, ?_, ?_⟩
    · rw [(D.base_segment ht).2.2]
      constructor <;> dsimp <;> linarith [ht.1, ht.2]
    · rw [(D.base_segment ht).2.2]

end VeechDichotomy.NativeBufferedFlowboxes.Data
