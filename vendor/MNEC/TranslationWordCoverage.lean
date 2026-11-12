module

public import MNEC.TranslationFlowWords

/-!
# Finite accepted physical words cover every native valid time

A genuine ball about a native trajectory point computes all nearby time
increments and their inverses. Finite-word reachability is therefore
relatively clopen in the actual connected maximal interval and contains
zero. No finite-partition, continuation or complete-orbit oracle occurs.
-/

noncomputable section
@[expose] public section

namespace MNEC.TranslationWordCoverage

open LatticeTorus TranslationBallCharts TranslationFlowWords Set Topology Filter
open scoped Classical Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Plane X]

def reachable (v : Plane) (x : X) : Set ℝ := {t | ∃ W : List (Step X), elapsed W = t ∧ x ∈ (wordMap v W).source}

theorem zero_reachable (v : Plane) (x : X) : 0 ∈ reachable v x := by
  refine ⟨[], rfl, ?_⟩
  rw [wordMap_nil]
  exact mem_univ _

variable [HasGroupoid X TranslationGroupoid.groupoid] [IsManifold 𝓘(ℝ, Plane) ∞ X] [T2Space X]

theorem reachable_subset_domain (v : Plane) (x : X) : reachable v x ⊆ TranslationAtlasCurves.domain v x := by
  rintro t ⟨W, htime, hx⟩
  rw [← htime]
  exact word_time_mem_domain v W x hx

theorem trajectory_locally_one_ball_step (v : Plane) (x : X) (s : ℝ) (hs : s ∈ TranslationAtlasCurves.domain v x) :
    ∃ B : BallChart X, TranslationAtlasCurves.trajectory v x s ∈ (model B).target ∧
      ∀ᶠ t in 𝓝 s, TranslationAtlasCurves.trajectory v x s ∈ (timeMap B v (t - s)).source ∧
        t ∈ TranslationAtlasCurves.domain v x ∧ timeMap B v (t - s) (TranslationAtlasCurves.trajectory v x s) = TranslationAtlasCurves.trajectory v x t := by
  obtain ⟨B, hB⟩ := exists_ballChart_at (TranslationAtlasCurves.trajectory v x s)
  have hzero := zero_mem_timeDomain B v (TranslationAtlasCurves.trajectory v x s) hB
  have hcenter : s - s ∈ timeDomain B v (TranslationAtlasCurves.trajectory v x s) := by simpa only [sub_self] using hzero
  have hcont : Continuous (fun t : ℝ => t - s) := continuous_id.sub continuous_const
  have hnear : ∀ᶠ t in 𝓝 s, t - s ∈ timeDomain B v (TranslationAtlasCurves.trajectory v x s) :=
    hcont.continuousAt ((timeDomain_open B v _).mem_nhds hcenter)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hnear] with t ht
  have hstep := (mem_timeMap_source B v (t - s) (TranslationAtlasCurves.trajectory v x s)).mpr ⟨hB, ht⟩
  obtain ⟨hδ, hvalue⟩ := timeMap_native_identification B v (t - s) (TranslationAtlasCurves.trajectory v x s) hstep
  have htD : t ∈ TranslationAtlasCurves.domain v x := by
    have h := hδ
    rw [TranslationAtlasCurves.domain_at_time v x s hs] at h
    change (t - s) + s ∈ TranslationAtlasCurves.domain v x at h
    simpa only [sub_add_cancel] using h
  refine ⟨hstep, htD, ?_⟩
  rw [hvalue]
  simpa only [sub_add_cancel] using TranslationAtlasCurves.trajectory_add v x s hs (t - s) hδ

theorem reachable_step (v : Plane) (x : X) (s t : ℝ) (hs : s ∈ reachable v x) (B : BallChart X)
    (hstep : TranslationAtlasCurves.trajectory v x s ∈ (timeMap B v (t - s)).source) : t ∈ reachable v x := by
  obtain ⟨W, htime, hx⟩ := hs
  refine ⟨W ++ [(B, t - s)], ?_, ?_⟩
  · rw [elapsed_append, elapsed_singleton, htime]
    ring
  · rw [mem_wordMap_append_source, wordMap_singleton]
    refine ⟨hx, ?_⟩
    rw [wordMap_eq_trajectory v W x hx, htime]
    exact hstep

theorem reachable_locally_constant (v : Plane) (x : X) (s : ℝ) (hs : s ∈ TranslationAtlasCurves.domain v x) :
    ∀ᶠ t in 𝓝 s, t ∈ TranslationAtlasCurves.domain v x ∧ (t ∈ reachable v x ↔ s ∈ reachable v x) := by
  obtain ⟨B, _, hnear⟩ := trajectory_locally_one_ball_step v x s hs
  filter_upwards [hnear] with t ht
  refine ⟨ht.2.1, ?_⟩
  constructor
  · intro hreach
    have hreverse := reverse_step_source B v (t - s) (TranslationAtlasCurves.trajectory v x s) ht.1
    rw [ht.2.2] at hreverse
    have hneg : -(t - s) = s - t := by ring
    rw [hneg] at hreverse
    exact reachable_step v x t s hreach B hreverse
  · intro hreach
    exact reachable_step v x s t hreach B ht.1

theorem reachable_open (v : Plane) (x : X) : IsOpen (reachable v x) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  apply Filter.mem_of_superset (reachable_locally_constant v x s (reachable_subset_domain v x hs))
  exact fun t ht => ht.2.mpr hs

theorem unreachable_in_domain_open (v : Plane) (x : X) : IsOpen (TranslationAtlasCurves.domain v x \ reachable v x) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro s ⟨hsD, hsR⟩
  apply Filter.mem_of_superset (reachable_locally_constant v x s hsD)
  exact fun t ht => ⟨ht.1, fun hreach => hsR (ht.2.mp hreach)⟩

/-- Every valid native time is realized by a finite word of actual accepted
convex physical ball steps. -/
theorem word_of_mem_domain (v : Plane) (x : X) (t : ℝ) (ht : t ∈ TranslationAtlasCurves.domain v x) :
    ∃ W : List (Step X), elapsed W = t ∧ x ∈ (wordMap v W).source := by
  let R := reachable v x
  let D := TranslationAtlasCurves.domain v x
  have hR : IsOpen R := reachable_open v x
  have hDR : IsOpen (D \ R) := unreachable_in_domain_open v x
  have hdisjoint : Disjoint R (D \ R) := disjoint_left.mpr (fun _ hr hnr => hnr.2 hr)
  have hcover : D ⊆ R ∪ (D \ R) := by
    intro s hs
    by_cases hr : s ∈ R
    · exact Or.inl hr
    · exact Or.inr ⟨hs, hr⟩
  have hnonempty : (D ∩ R).Nonempty := ⟨0, TranslationAtlasCurves.zero_mem_domain v x, zero_reachable v x⟩
  have hsub : D ⊆ R := IsPreconnected.subset_left_of_subset_union hR hDR hdisjoint hcover hnonempty
    (TranslationAtlasCurves.domain_connected v x).isPreconnected
  exact hsub ht

theorem timeSource_eq_words (v : Plane) (t : ℝ) :
    {x : X | t ∈ TranslationAtlasCurves.domain v x} = ⋃ (W : List (Step X)) (_ : elapsed W = t), (wordMap v W).source := by
  ext x
  constructor
  · intro hx
    obtain ⟨W, htime, hsource⟩ := word_of_mem_domain v x t hx
    exact mem_iUnion.mpr ⟨W, mem_iUnion.mpr ⟨htime, hsource⟩⟩
  · intro hx
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    obtain ⟨htime, hsource⟩ := mem_iUnion.mp hx
    have h := word_time_mem_domain v W x hsource
    rwa [htime] at h

end MNEC.TranslationWordCoverage

