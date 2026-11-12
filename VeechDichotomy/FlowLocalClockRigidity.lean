module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-! A map commuting with a free dense real-flow orbit cannot have a
nonconstant continuous local time displacement. The physical observation
space may differ from the complete phase space, as for native surfaces. -/

@[expose] public section

namespace VeechDichotomy.FlowLocalClockRigidity

open Set Filter Topology

variable {Ω X : Type*} [TopologicalSpace Ω] [TopologicalSpace X]

theorem constant_on_open (F : Flow ℝ Ω) (ι : Ω → X) (f : Ω → Ω)
    (hcomm : ∀ t y, f (F t y) = F t (f y)) (x : Ω)
    (hinj : Function.Injective (fun t : ℝ => F t x))
    (hdense : DenseRange (fun t : ℝ => ι (F t x)))
    (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) (τ : X → ℝ) (hτ : ContinuousOn τ U)
    (hlocal : ∀ y : Ω, ι y ∈ U → f y = F (τ (ι y)) y) :
    ∃ c : ℝ, ∀ y ∈ U, τ y = c := by
  obtain ⟨s, hs⟩ := hdense.exists_mem_open hU hne
  let c := τ (ι (F s x))
  have hbase : f (F s x) = F c (F s x) := hlocal _ hs
  have hfx : f x = F c x := by
    calc
      f x = F (-s) (F s (f x)) := by rw [← F.map_add, neg_add_cancel, Flow.map_zero_apply]
      _ = F (-s) (f (F s x)) := by rw [hcomm]
      _ = F (-s) (F c (F s x)) := by rw [hbase]
      _ = F c x := by rw [← F.map_add, ← F.map_add]; congr 1; ring
  have horbit : ∀ t : ℝ, ι (F t x) ∈ U → τ (ι (F t x)) = c := by
    intro t ht
    have heq : F (τ (ι (F t x)) + t) x = F (c + t) x := by
      calc
        F (τ (ι (F t x)) + t) x = F (τ (ι (F t x))) (F t x) := F.map_add _ _ _
        _ = f (F t x) := (hlocal _ ht).symm
        _ = F t (f x) := hcomm _ _
        _ = F t (F c x) := by rw [hfx]
        _ = F (c + t) x := by rw [← F.map_add, add_comm]
    exact add_right_cancel (hinj heq)
  refine ⟨c, ?_⟩
  intro y hy
  by_contra hneC
  let V := U ∩ τ ⁻¹' ({c} : Set ℝ)ᶜ
  have hV : IsOpen V := hτ.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hyV : y ∈ V := ⟨hy, hneC⟩
  obtain ⟨t, ht⟩ := hdense.exists_mem_open hV ⟨y, hyV⟩
  exact ht.2 (horbit t ht.1)

end VeechDichotomy.FlowLocalClockRigidity
