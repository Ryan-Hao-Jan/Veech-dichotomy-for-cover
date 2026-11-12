module

public import VeechDichotomy.NativeFlowboxBaseArcs
public import VeechDichotomy.NativeFlowboxProfileSets

/-! Geometric intersections with a concrete flowbox base are the actual
closed-base crossing counts on minimal complete native orbits. Their
finiteness follows from local chart separation even without minimality. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBufferedFlowboxes.Data

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeMinimalOrbitVisits Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} (D : NativeBufferedFlowboxes.Data q)

theorem closed_hits_separated (x : CompleteOrbits q vertical) :
    SeparatedWindowCounts.Separated D.height (D.closedHits x) := by
  have hs := NativeVerticalFlowboxes.separated_hits q D.index (le_refl D.outerLeft) (le_refl D.outerRight)
    D.bottom_buffer D.top_buffer D.target x
  apply hs.mono
  intro t ht
  exact ⟨ht.1, ⟨D.left_buffer.trans_le ht.2.1.1, ht.2.1.2.trans_lt D.right_buffer⟩, ht.2.2⟩

theorem finite_closed_hits (x : CompleteOrbits q vertical) (a b : ℝ) :
    (D.closedHits x ∩ Icc a b).Finite :=
  SeparatedWindowCounts.finite_window D.height_pos (D.closed_hits_separated x) a b

theorem visits_eq_closed_hits (x : CompleteOrbits q vertical) (a b : ℝ) :
    visits q vertical x D.baseSet a b = D.closedHits x ∩ Icc a b := rfl

theorem finite_base_intersections (x : CompleteOrbits q vertical) (a b : ℝ) :
    (trajectory q vertical x.val '' Icc a b ∩
      trajectory q horizontal D.basePoint '' Icc 0 (D.right - D.left)).Finite := by
  rw [← D.baseSet_eq_arc, inter_comm, intersection_eq_image, D.visits_eq_closed_hits]
  exact (D.finite_closed_hits x a b).image _

theorem base_intersection_count (hmin : NativeDynamics.MinimalDirection q vertical)
    (x : CompleteOrbits q vertical) (a b : ℝ) :
    (trajectory q vertical x.val '' Icc a b ∩
      trajectory q horizontal D.basePoint '' Icc 0 (D.right - D.left)).ncard =
        SeparatedWindowCounts.count (D.closedHits x) a b := by
  rw [← D.baseSet_eq_arc, inter_comm, intersection_count_eq q vertical hmin x,
    D.visits_eq_closed_hits]
  rfl

theorem base_intersection_rate (hmin : NativeDynamics.MinimalDirection q vertical)
    (x : CompleteOrbits q vertical) (R : ℕ → ℝ) {m : ℝ}
    (hp : NativeFlowboxProfileSets.CrossingProfile q D R x m)
    {A B : ℕ → ℝ} {a b : ℝ} (hA : Tendsto (fun k => A k / R k) atTop (𝓝 a))
    (hB : Tendsto (fun k => B k / R k) atTop (𝓝 b)) (hab : a < b) :
    Tendsto (fun k => ((trajectory q vertical x.val '' Icc (A k) (B k) ∩
      trajectory q horizontal D.basePoint '' Icc 0 (D.right - D.left)).ncard : ℝ) /
        (B k - A k)) atTop (𝓝 (m / D.height)) := by
  simp_rw [D.base_intersection_count hmin x]
  exact hp A B a b hA hB hab

end VeechDichotomy.NativeBufferedFlowboxes.Data
