module

public import VeechDichotomy.NativeFlowboxCoordinateMeasures

/-! Clipping an actual native flowbox by an arbitrary coordinate rectangle
produces either the empty set or another concrete buffered native flowbox.
The new box retains the actual outer primitive rectangle and its buffers. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBufferedFlowboxes.Data

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles MeasureTheory Set
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} (D : NativeBufferedFlowboxes.Data q)

theorem clipped_or_empty (l r b t : ℝ) :
    (D.phaseRegion ∩ {x | chart q D.index x.val ∈ rectangle l r b t}) = ∅ ∨
      ∃ E : NativeBufferedFlowboxes.Data q,
        E.phaseRegion = D.phaseRegion ∩ {x | chart q D.index x.val ∈ rectangle l r b t} := by
  let S := D.phaseRegion ∩ {x | chart q D.index x.val ∈ rectangle l r b t}
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hdx : (chart q D.index x.val).1 ∈ Ioo D.left D.right ∧
        (chart q D.index x.val).2 ∈ Ioo D.bottom (D.bottom + D.height) := hx.1.2
    have hax : (chart q D.index x.val).1 ∈ Ioo l r ∧ (chart q D.index x.val).2 ∈ Ioo b t := hx.2
    let L := max D.left l
    let R := min D.right r
    let B := max D.bottom b
    let T := min (D.bottom + D.height) t
    have hLR : L < R := (max_lt_iff.mpr ⟨hdx.1.1, hax.1.1⟩).trans (lt_min_iff.mpr ⟨hdx.1.2, hax.1.2⟩)
    have hBT : B < T := (max_lt_iff.mpr ⟨hdx.2.1, hax.2.1⟩).trans (lt_min_iff.mpr ⟨hdx.2.2, hax.2.2⟩)
    let E : NativeBufferedFlowboxes.Data q := {
      index := D.index
      left := L, right := R, bottom := B, height := T - B
      outerLeft := D.outerLeft, outerRight := D.outerRight, outerBottom := D.outerBottom, outerTop := D.outerTop
      width_pos := hLR
      height_pos := sub_pos.mpr hBT
      left_buffer := D.left_buffer.trans_le (le_max_left _ _)
      right_buffer := (min_le_left _ _).trans_lt D.right_buffer
      bottom_buffer := D.bottom_buffer.trans_le (le_max_left _ _)
      top_buffer := by
        have htop : T < D.outerTop := (min_le_left _ _).trans_lt D.top_buffer
        linarith
      target := D.target }
    right
    refine ⟨E, ?_⟩
    ext y
    change (y.val ∈ (chart q D.index).source ∧ chart q D.index y.val ∈ rectangle L R B (B + (T - B))) ↔
      (y.val ∈ (chart q D.index).source ∧ chart q D.index y.val ∈ rectangle D.left D.right D.bottom (D.bottom + D.height)) ∧
        chart q D.index y.val ∈ rectangle l r b t
    rw [show B + (T - B) = T by ring]
    simp only [rectangle, mem_prod, mem_Ioo, L, R, B, T, max_lt_iff, lt_min_iff]
    tauto
  · left
    exact not_nonempty_iff_eq_empty.mp hS

end VeechDichotomy.NativeBufferedFlowboxes.Data
