module

public import VeechDichotomy.FlowIntegerAverages
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith

/-! Every injective continuous real-flow orbit has measure zero for
any finite invariant measure. A measurable unit half-open orbit segment
is wandering for time one, so proved conservativity forces zero mass;
integer translates then cover the entire actual orbit. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FreeFlowOrbitNull

open MeasureTheory Set Filter Topology

variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω] [MeasurableSpace Ω] [BorelSpace Ω]
variable (F : Flow ℝ Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (hF : ∀ t, MeasurePreserving (F t) μ μ)

include hF in
theorem orbit_null (x : Ω) (hinj : Function.Injective (fun t : ℝ => F t x)) :
    μ (range (fun t : ℝ => F t x)) = 0 := by
  let A := (fun t : ℝ => F t x) '' Ico 0 1
  have hAeq : A = (fun t : ℝ => F t x) '' Icc 0 1 \ {F 1 x} := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩, ?_⟩
      intro hy
      have heq := hinj (mem_singleton_iff.mp hy)
      linarith [hs.2]
    · rintro ⟨⟨s, hs, rfl⟩, hne⟩
      refine ⟨s, ⟨hs.1, ?_⟩, rfl⟩
      by_contra hnot
      have heq : s = 1 := le_antisymm hs.2 (le_of_not_gt hnot)
      exact hne (mem_singleton_iff.mpr (congrArg (fun t : ℝ => F t x) heq))
  have hA : MeasurableSet A := by
    rw [hAeq]
    exact (isCompact_Icc.image (F.continuous continuous_id continuous_const)).isClosed.measurableSet.diff (measurableSet_singleton _)
  have hzero : μ A = 0 := by
    by_contra h0
    obtain ⟨n, hn, hret⟩ := (hF 1).conservative.exists_gt_measure_inter_ne_zero hA.nullMeasurableSet h0 0
    have hempty : A ∩ (F 1)^[n] ⁻¹' A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨s, hs, rfl⟩ := hy.1
      obtain ⟨t, ht, heq⟩ := hy.2
      rw [FlowIntegerAverages.iterate_one, ← F.map_add] at heq
      have htime : t = (n : ℝ) + s := hinj heq
      have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
      linarith [hs.1, ht.2]
    rw [hempty, measure_empty] at hret
    exact hret rfl
  have htranslate : ∀ t : ℝ, μ (F t '' A) = 0 := by
    intro t
    have heq : F t '' A = F (-t) ⁻¹' A := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change F (-t) (F t z) ∈ A
        rwa [← F.map_add, neg_add_cancel, Flow.map_zero_apply]
      · intro hy
        refine ⟨F (-t) y, hy, ?_⟩
        rw [← F.map_add, add_neg_cancel, Flow.map_zero_apply]
    rw [heq, (hF (-t)).measure_preimage hA.nullMeasurableSet, hzero]
  have hcover : range (fun t : ℝ => F t x) ⊆ ⋃ k : ℤ, F (k : ℝ) '' A := by
    rintro y ⟨s, rfl⟩
    let k := Int.floor s
    have hu : s - (k : ℝ) ∈ Ico (0 : ℝ) 1 := by
      constructor <;> linarith [Int.floor_le s, Int.lt_floor_add_one s]
    refine mem_iUnion.mpr ⟨k, F (s - (k : ℝ)) x, ⟨s - (k : ℝ), hu, rfl⟩, ?_⟩
    rw [← F.map_add]
    congr 1
    ring
  exact measure_mono_null hcover (measure_iUnion_null (fun k : ℤ => htranslate k))

def reaching (x : Ω) : Set Ω := {y | ∃ t : ℝ, F t y = x}

omit [T2Space Ω] [MeasurableSpace Ω] [BorelSpace Ω] [IsFiniteMeasure μ] in
theorem reaching_eq_range (x : Ω) : reaching F x = range (fun t : ℝ => F t x) := by
  ext y
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    change F (-t) x = y
    rw [← ht, ← F.map_add, neg_add_cancel, Flow.map_zero_apply]
  · rintro ⟨t, rfl⟩
    exact ⟨-t, by rw [← F.map_add, neg_add_cancel, Flow.map_zero_apply]⟩

include hF in
theorem reaching_null (x : Ω) (hinj : Function.Injective (fun t : ℝ => F t x)) : μ (reaching F x) = 0 := by
  rw [reaching_eq_range]
  exact orbit_null F μ hF x hinj

end VeechDichotomy.FreeFlowOrbitNull
