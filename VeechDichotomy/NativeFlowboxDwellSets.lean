module

public import VeechDichotomy.NativeVerticalFlowboxes
public import VeechDichotomy.SeparatedDwellVolume

/-! Along the actual complete native vertical flow, the times in a
buffered open flowbox are exactly the length-height intervals following
actual hits of its horizontal base. No return-time oracle is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFlowboxDwellSets

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeVerticalFlowboxes Set MeasureTheory Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

def occupancy (x : CompleteOrbits q vertical) (l r b h : ℝ) : Set ℝ :=
  {t | (timeMap q vertical t x).val ∈ box q i l r b h}

theorem occupancy_open (x : CompleteOrbits q vertical) (l r b h : ℝ) :
    IsOpen (occupancy q i x l r b h) := by
  exact (box_open q i l r b h).preimage
    (continuous_subtype_val.comp
      ((continuous_joint_timeMap q vertical).comp (continuous_id.prodMk continuous_const)))

theorem occupancy_eq_blocks {l0 r0 b0 u0 l r b h : ℝ}
    (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) :
    occupancy q i x l r b h = SeparatedDwellVolume.blocks (hitTimes q i x l r b) h := by
  ext t
  constructor
  · intro ht
    have hy : (timeMap q vertical t x).val ∈ box q i l r b h := ht
    let y := timeMap q vertical t x
    let d := (chart q i y.val).2 - b
    have hd : d ∈ Ioo 0 h := by
      constructor <;> dsimp [d, y] <;> linarith [hy.2.2.1, hy.2.2.2]
    have hyr : chart q i y.val ∈ rectangle l0 r0 b0 u0 :=
      ⟨⟨lt_of_le_of_lt hl hy.2.1.1, lt_of_lt_of_le hy.2.1.2 hr⟩,
        ⟨by linarith [hy.2.2.1], by linarith [hy.2.2.2]⟩⟩
    have hneg : -d ∈ Ioo (b0 - (chart q i y.val).2) (u0 - (chart q i y.val).2) := by
      constructor <;> dsimp [d] <;> linarith [hd.1, hd.2]
    have hc := coordinates q i hR y hy.1 hyr hneg
    have heq : timeMap q vertical (-d) y = timeMap q vertical (t - d) x := by
      dsimp [y]
      rw [← timeMap_add]
      congr 1
      ring
    rw [heq] at hc
    have hs : t - d ∈ hitTimes q i x l r b := by
      refine ⟨hc.1, ?_, ?_⟩
      · have hx := congrArg Prod.fst hc.2
        change (chart q i (timeMap q vertical (t - d) x).val).1 = (chart q i y.val).1 at hx
        rw [hx]
        exact hy.2.1
      · have hz := congrArg Prod.snd hc.2
        change (chart q i (timeMap q vertical (t - d) x).val).2 = (chart q i y.val).2 + -d at hz
        rw [hz]
        dsimp [d]
        ring
    exact mem_iUnion₂.mpr ⟨t - d, hs, by constructor <;> linarith [hd.1, hd.2]⟩
  · intro ht
    rcases mem_iUnion₂.mp ht with ⟨s, hs, hst⟩
    have hdelta : t - s ∈ Icc 0 h := by
      constructor <;> linarith [hst.1, hst.2]
    have hc := base_coordinates q i hl hr hb hu hR (timeMap q vertical s x) hs hdelta
    have heq : timeMap q vertical (t - s) (timeMap q vertical s x) = timeMap q vertical t x := by
      rw [← timeMap_add, sub_add_cancel]
    rw [heq] at hc
    change (timeMap q vertical t x).val ∈ box q i l r b h
    refine ⟨hc.1, ?_⟩
    change chart q i (timeMap q vertical t x).val ∈ rectangle l r b (b + h)
    rw [hc.2]
    exact ⟨hs.2.1, by constructor <;> linarith [hst.1, hst.2]⟩

theorem dwell_error {l0 r0 b0 u0 l r b h : ℝ}
    (hh : 0 < h) (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) (a z : ℝ) :
    |volume.real (occupancy q i x l r b h ∩ Ioc a z) -
      h * (SeparatedWindowCounts.count (hitTimes q i x l r b) a z : ℝ)| ≤ h := by
  rw [occupancy_eq_blocks q i hl hr hb hu hR x]
  exact SeparatedDwellVolume.window_error hh (separated_hits q i hl hr hb hu hR x) a z

end VeechDichotomy.NativeFlowboxDwellSets
