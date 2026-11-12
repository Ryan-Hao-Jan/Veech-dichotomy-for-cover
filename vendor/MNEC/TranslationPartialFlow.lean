module

public import MNEC.TranslationWordCoverage

/-!
# Actual fixed-time partial homeomorphisms of a translation atlas

Finite accepted words prove openness and continuity of the actual maximal
fixed-time map. Native reversal supplies its exact inverse at time `-t`.
Every defined point has an open neighborhood computed by one finite actual
word. Completeness is not an input or conclusion.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationPartialFlow

open LatticeTorus TranslationFlowWords Set Topology Filter
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]

def timeSource (v : Plane) (t : ℝ) : Set X := {x | t ∈ TranslationAtlasCurves.domain v x}

variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X] [T2Space X]

theorem timeSource_eq_words (v : Plane) (t : ℝ) :
    timeSource (X := X) v t = ⋃ (W : List (Step X)) (_ : elapsed W = t), (wordMap v W).source :=
  TranslationWordCoverage.timeSource_eq_words v t

theorem timeSource_open (v : Plane) (t : ℝ) : IsOpen (timeSource (X := X) v t) := by
  rw [timeSource_eq_words]
  exact isOpen_iUnion fun W => isOpen_iUnion fun _ => (wordMap v W).open_source

theorem continuousAt_trajectory_time (v : Plane) (t : ℝ) (x : X) (hx : x ∈ timeSource v t) :
    ContinuousAt (fun y => TranslationAtlasCurves.trajectory v y t) x := by
  obtain ⟨W, htime, hsource⟩ := TranslationWordCoverage.word_of_mem_domain v x t hx
  apply ((wordMap v W).continuousAt hsource).congr_of_eventuallyEq
  filter_upwards [(wordMap v W).open_source.mem_nhds hsource] with y hy
  have h := wordMap_eq_trajectory v W y hy
  rw [htime] at h
  exact h.symm

theorem continuousOn_trajectory_time (v : Plane) (t : ℝ) :
    ContinuousOn (fun x : X => TranslationAtlasCurves.trajectory v x t) (timeSource v t) :=
  fun x hx => (continuousAt_trajectory_time v t x hx).continuousWithinAt

def timeMap (v : Plane) (t : ℝ) : OpenPartialHomeomorph X X where
  toFun x := TranslationAtlasCurves.trajectory v x t
  invFun x := TranslationAtlasCurves.trajectory v x (-t)
  source := timeSource v t
  target := timeSource v (-t)
  map_source' x hx := (TranslationAtlasCurves.reverse_time v x t hx).1
  map_target' x hx := by
    change t ∈ TranslationAtlasCurves.domain v (TranslationAtlasCurves.trajectory v x (-t))
    simpa only [neg_neg] using (TranslationAtlasCurves.reverse_time v x (-t) hx).1
  left_inv' x hx := (TranslationAtlasCurves.reverse_time v x t hx).2
  right_inv' x hx := by
    simpa only [neg_neg] using (TranslationAtlasCurves.reverse_time v x (-t) hx).2
  continuousOn_toFun := continuousOn_trajectory_time v t
  continuousOn_invFun := continuousOn_trajectory_time v (-t)
  open_source := timeSource_open v t
  open_target := timeSource_open v (-t)

theorem timeMap_apply (v : Plane) (t : ℝ) (x : X) : timeMap v t x = TranslationAtlasCurves.trajectory v x t := rfl
theorem timeMap_source (v : Plane) (t : ℝ) : (timeMap (X := X) v t).source = timeSource v t := rfl
theorem timeMap_target (v : Plane) (t : ℝ) : (timeMap (X := X) v t).target = timeSource v (-t) := rfl
theorem timeMap_symm_apply (v : Plane) (t : ℝ) (x : X) : (timeMap v t).symm x = TranslationAtlasCurves.trajectory v x (-t) := rfl

theorem timeMap_locally_word (v : Plane) (t : ℝ) (x : X) (hx : x ∈ (timeMap v t).source) :
    ∃ W : List (Step X), elapsed W = t ∧ x ∈ (wordMap v W).source ∧ ∀ᶠ y in 𝓝 x, timeMap v t y = wordMap v W y := by
  obtain ⟨W, htime, hsource⟩ := TranslationWordCoverage.word_of_mem_domain v x t hx
  refine ⟨W, htime, hsource, ?_⟩
  filter_upwards [(wordMap v W).open_source.mem_nhds hsource] with y hy
  have h := wordMap_eq_trajectory v W y hy
  rw [htime] at h
  exact h.symm

theorem timeMap_add (v : Plane) (s t : ℝ) (x : X) (hs : x ∈ (timeMap v s).source)
    (ht : timeMap v s x ∈ (timeMap v t).source) :
    timeMap v t (timeMap v s x) = timeMap v (s + t) x :=
  (TranslationAtlasCurves.trajectory_add v x s hs t ht).trans (congrArg (TranslationAtlasCurves.trajectory v x) (add_comm t s))

end MNEC.TranslationPartialFlow

