module

public import VeechDichotomy.NativeFlowboxIntersectionCounts

/-! Exact translation of complete native orbit segments and flowbox
crossing windows. This permits a source point to move by a known native
flow time while retaining statistics of the original fixed point. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCompleteOrbitShifts

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeBufferedFlowboxes Set
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

theorem trajectory_shift (x : CompleteOrbits q v) (a t : ℝ) :
    trajectory q v (timeMap q v a x).val t = trajectory q v x.val (t + a) := by
  exact congrArg Subtype.val (timeMap_add q v t a x).symm

theorem image_interval (x : CompleteOrbits q v) (a b c : ℝ) :
    trajectory q v (timeMap q v a x).val '' Icc b c = trajectory q v x.val '' Icc (b + a) (c + a) := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t + a, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (trajectory_shift q v x a t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t - a, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [trajectory_shift, sub_add_cancel]

theorem closed_hits_shift (D : Data q) (x : CompleteOrbits q vertical) (a t : ℝ) :
    t ∈ D.closedHits (timeMap q vertical a x) ↔ t + a ∈ D.closedHits x := by
  change (timeMap q vertical t (timeMap q vertical a x)).val ∈ D.baseSet ↔
    (timeMap q vertical (t + a) x).val ∈ D.baseSet
  rw [← timeMap_add]

theorem closed_count_shift (D : Data q) (x : CompleteOrbits q vertical) (a b c : ℝ) :
    SeparatedWindowCounts.count (D.closedHits (timeMap q vertical a x)) b c =
      SeparatedWindowCounts.count (D.closedHits x) (b + a) (c + a) := by
  have heq := SeparatedWindowCounts.translate_window_count a (b + a) (c + a) (closed_hits_shift q D x a)
  simpa only [add_sub_cancel_right] using heq.symm

end VeechDichotomy.NativeCompleteOrbitShifts
