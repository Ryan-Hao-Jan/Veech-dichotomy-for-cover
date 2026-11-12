module

public import MNEC.NativeDirectionalDynamics
public import MNEC.TranslationJointFlow
public import MNEC.TranslationFlowDifferentials

/-! Actual maximal partial directional maps on an ARBITRARY original
native differential. Its independently constructed primitive atlas
supplies every smooth/groupoid instance. Finite accepted physical words
give native domain coverage, open partial homeomorphisms, exact inverse
time, and joint velocity/time/point continuity. No flow or completeness
certificate is an input. -/

@[expose] public section
noncomputable section
namespace MNEC.NativePartialDirectionalFlow

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas Set Filter Topology
open scoped Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

abbrev Step (q : Differential X) := letI := chartedSpace q; TranslationFlowWords.Step (Regular q)

def elapsed (q : Differential X) (W : List (Step q)) : ℝ := by
  let := chartedSpace q
  exact TranslationFlowWords.elapsed W

def wordMap (q : Differential X) (v : Plane) (W : List (Step q)) :
    OpenPartialHomeomorph (Regular q) (Regular q) := by
  let := chartedSpace q
  exact TranslationFlowWords.wordMap v W

theorem word_native_identification (q : Differential X) (v : Plane) (W : List (Step q))
    (x : Regular q) (hx : x ∈ (wordMap q v W).source) :
    elapsed q W ∈ NativeDirectionalDynamics.domain q v x ∧
      wordMap q v W x = NativeDirectionalDynamics.trajectory q v x (elapsed q W) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationFlowWords.word_native_identification (X := Regular q) v W x hx

theorem word_of_mem_domain (q : Differential X) (v : Plane) (x : Regular q) (t : ℝ)
    (ht : t ∈ NativeDirectionalDynamics.domain q v x) :
    ∃ W : List (Step q), elapsed q W = t ∧ x ∈ (wordMap q v W).source := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationWordCoverage.word_of_mem_domain (X := Regular q) v x t ht

def valid (q : Differential X) : Set (Plane × ℝ × Regular q) :=
  {p | p.2.1 ∈ NativeDirectionalDynamics.domain q p.1 p.2.2}

def jointTrajectory (q : Differential X) (p : Plane × ℝ × Regular q) : Regular q :=
  NativeDirectionalDynamics.trajectory q p.1 p.2.2 p.2.1

def timeSource (q : Differential X) (v : Plane) (t : ℝ) : Set (Regular q) :=
  {x | t ∈ NativeDirectionalDynamics.domain q v x}

def timeMap (q : Differential X) (v : Plane) (t : ℝ) :
    OpenPartialHomeomorph (Regular q) (Regular q) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationPartialFlow.timeMap v t

theorem timeMap_apply (q : Differential X) (v : Plane) (t : ℝ) (x : Regular q) :
    timeMap q v t x = NativeDirectionalDynamics.trajectory q v x t := rfl

theorem timeMap_source (q : Differential X) (v : Plane) (t : ℝ) :
    (timeMap q v t).source = timeSource q v t := rfl

theorem timeMap_target (q : Differential X) (v : Plane) (t : ℝ) :
    (timeMap q v t).target = timeSource q v (-t) := rfl

theorem timeMap_symm_apply (q : Differential X) (v : Plane) (t : ℝ) (x : Regular q) :
    (timeMap q v t).symm x = NativeDirectionalDynamics.trajectory q v x (-t) := rfl

theorem timeSource_open (q : Differential X) (v : Plane) (t : ℝ) : IsOpen (timeSource q v t) :=
  (timeMap q v t).open_source

theorem reverse_time_value (q : Differential X) (v : Plane) (t : ℝ) (x : Regular q)
    (hx : x ∈ (timeMap q v t).source) : timeMap q v (-t) (timeMap q v t x) = x :=
  (timeMap q v t).left_inv hx

theorem timeMap_add (q : Differential X) (v : Plane) (s t : ℝ) (x : Regular q)
    (hs : x ∈ (timeMap q v s).source) (ht : timeMap q v s x ∈ (timeMap q v t).source) :
    timeMap q v t (timeMap q v s x) = timeMap q v (s + t) x :=
  (NativeDirectionalDynamics.trajectory_add q v x s hs t ht).trans
    (congrArg (NativeDirectionalDynamics.trajectory q v x) (add_comm t s))

theorem valid_open (q : Differential X) : IsOpen (valid q) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationJointFlow.valid_open (X := Regular q)

theorem continuousAt_jointTrajectory (q : Differential X) (p : Plane × ℝ × Regular q)
    (hp : p ∈ valid q) : ContinuousAt (jointTrajectory q) p := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationJointFlow.continuousAt_value (X := Regular q) p hp

theorem continuousOn_jointTrajectory (q : Differential X) : ContinuousOn (jointTrajectory q) (valid q) :=
  fun p hp => (continuousAt_jointTrajectory q p hp).continuousWithinAt

theorem timeMap_locally_word (q : Differential X) (v : Plane) (t : ℝ) (x : Regular q)
    (hx : x ∈ (timeMap q v t).source) :
    ∃ W : List (Step q), elapsed q W = t ∧ x ∈ (wordMap q v W).source ∧
      ∀ᶠ y in 𝓝 x, timeMap q v t y = wordMap q v W y := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationPartialFlow.timeMap_locally_word (X := Regular q) v t x hx

theorem timeMap_locally_physical_translation (q : Differential X) (v : Plane) (t : ℝ)
    (i j x : Regular q) (hx : x ∈ (timeMap q v t).source)
    (hxi : x ∈ (coordinateChart q i).source) (hxj : timeMap q v t x ∈ (coordinateChart q j).source) :
    ∃ c : Plane, ∀ᶠ p in 𝓝 (coordinateChart q i x),
      coordinateChart q j (timeMap q v t ((coordinateChart q i).symm p)) = p + c := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  have hi : coordinateChart q i ∈ atlas Plane (Regular q) := ⟨i, rfl⟩
  have hj : coordinateChart q j ∈ atlas Plane (Regular q) := ⟨j, rfl⟩
  exact TranslationFlowDifferentials.timeMap_locally_physical_translation (X := Regular q) v t
    (coordinateChart q i) (coordinateChart q j) hi hj x hx hxi hxj

end MNEC.NativePartialDirectionalFlow

