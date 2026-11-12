module

public import MNEC.TranslationBallCharts
public import MNEC.DirectionalFlowWords

/-!
# Finite accepted physical words in a native translation atlas

The compositional machinery is purely topological. The native identification
uses the proved convex-ball interval solutions and autonomous maximal laws,
so no letter can jump between two disconnected parts of a general chart.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationFlowWords

open LatticeTorus TranslationBallCharts Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]

abbrev Step (X : Type*) [TopologicalSpace X] [ChartedSpace Plane X] := BallChart X × ℝ

def elapsed (W : List (Step X)) : ℝ := DirectionalFlowWords.duration (fun S => S.2) W
def stepMap (v : Plane) (S : Step X) : OpenPartialHomeomorph X X := timeMap S.1 v S.2
def wordMap (v : Plane) (W : List (Step X)) : OpenPartialHomeomorph X X := DirectionalFlowWords.compose (stepMap v) W

@[simp] theorem elapsed_nil : elapsed ([] : List (Step X)) = 0 := rfl
@[simp] theorem elapsed_cons (S : Step X) (W : List (Step X)) : elapsed (S :: W) = S.2 + elapsed W := rfl

theorem elapsed_append (W Z : List (Step X)) : elapsed (W ++ Z) = elapsed W + elapsed Z := DirectionalFlowWords.duration_append _ W Z

@[simp] theorem elapsed_singleton (S : Step X) : elapsed [S] = S.2 := by rw [elapsed_cons, elapsed_nil, add_zero]

@[simp] theorem wordMap_nil (v : Plane) : wordMap v ([] : List (Step X)) = OpenPartialHomeomorph.refl X := rfl
theorem wordMap_cons (v : Plane) (S : Step X) (W : List (Step X)) :
    wordMap v (S :: W) = (timeMap S.1 v S.2).trans (wordMap v W) := rfl

@[simp] theorem wordMap_singleton (v : Plane) (S : Step X) : wordMap v [S] = timeMap S.1 v S.2 := by
  rw [wordMap_cons, wordMap_nil, OpenPartialHomeomorph.trans_refl]

theorem wordMap_append (v : Plane) (W Z : List (Step X)) :
    wordMap v (W ++ Z) = (wordMap v W).trans (wordMap v Z) := DirectionalFlowWords.compose_append _ W Z

theorem mem_wordMap_append_source (v : Plane) (W Z : List (Step X)) (x : X) :
    x ∈ (wordMap v (W ++ Z)).source ↔ x ∈ (wordMap v W).source ∧ wordMap v W x ∈ (wordMap v Z).source := by
  rw [wordMap_append]
  rfl

variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X] [T2Space X]

theorem word_native_identification (v : Plane) (W : List (Step X)) (x : X) (hx : x ∈ (wordMap v W).source) :
    elapsed W ∈ TranslationAtlasCurves.domain v x ∧ wordMap v W x = TranslationAtlasCurves.trajectory v x (elapsed W) := by
  induction W generalizing x with
  | nil =>
    refine ⟨TranslationAtlasCurves.zero_mem_domain v x, ?_⟩
    exact (TranslationAtlasCurves.trajectory_initial v x).symm
  | cons S W ih =>
    have hxFirst : x ∈ (timeMap S.1 v S.2).source := hx.1
    have hxRest : timeMap S.1 v S.2 x ∈ (wordMap v W).source := hx.2
    obtain ⟨ht, hvalue⟩ := timeMap_native_identification S.1 v S.2 x hxFirst
    obtain ⟨hs, hrest⟩ := ih _ hxRest
    have hs' : elapsed W ∈ TranslationAtlasCurves.domain v (TranslationAtlasCurves.trajectory v x S.2) := by
      rw [← hvalue]
      exact hs
    have htotal : elapsed W + S.2 ∈ TranslationAtlasCurves.domain v x := by
      have h := hs'
      rw [TranslationAtlasCurves.domain_at_time v x S.2 ht] at h
      exact h
    constructor
    · simpa only [elapsed_cons, add_comm] using htotal
    · change wordMap v W (timeMap S.1 v S.2 x) = TranslationAtlasCurves.trajectory v x (S.2 + elapsed W)
      calc
        wordMap v W (timeMap S.1 v S.2 x) = TranslationAtlasCurves.trajectory v (timeMap S.1 v S.2 x) (elapsed W) := hrest
        _ = TranslationAtlasCurves.trajectory v (TranslationAtlasCurves.trajectory v x S.2) (elapsed W) := by rw [hvalue]
        _ = TranslationAtlasCurves.trajectory v x (elapsed W + S.2) := TranslationAtlasCurves.trajectory_add v x S.2 ht (elapsed W) hs'
        _ = TranslationAtlasCurves.trajectory v x (S.2 + elapsed W) := by rw [add_comm]

theorem word_time_mem_domain (v : Plane) (W : List (Step X)) (x : X) (hx : x ∈ (wordMap v W).source) :
    elapsed W ∈ TranslationAtlasCurves.domain v x := (word_native_identification v W x hx).1

theorem wordMap_eq_trajectory (v : Plane) (W : List (Step X)) (x : X) (hx : x ∈ (wordMap v W).source) :
    wordMap v W x = TranslationAtlasCurves.trajectory v x (elapsed W) := (word_native_identification v W x hx).2

end MNEC.TranslationFlowWords

