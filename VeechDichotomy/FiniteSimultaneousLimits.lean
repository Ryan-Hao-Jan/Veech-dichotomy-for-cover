module

public import Mathlib.Topology.Sequences
public import Mathlib.Data.Fintype.Basic

/-! Finitely many fixed-point limits can be selected along one common
strictly increasing subsequence, provided the selection argument works
after restriction to every subsequence. Earlier limits are preserved
by further restriction. -/

@[expose] public section

namespace VeechDichotomy.FiniteSimultaneousLimits

open Set Filter Topology

variable {I Z T : Type*} [Finite I] [TopologicalSpace T]

theorem simultaneous (f : ℕ → Z → T) (R : I → Z → T → Prop)
    (hselect : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
      ∃ (z : Z) (y : T) (ψ : ℕ → ℕ), StrictMono ψ ∧ R i z y ∧
        Tendsto (fun n => f (φ (ψ n)) z) atTop (𝓝 y)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i, ∃ (z : Z) (y : T), R i z y ∧
      Tendsto (fun n => f (σ n) z) atTop (𝓝 y) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hfin : ∀ s : Finset I, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ i ∈ s,
      ∃ (z : Z) (y : T), R i z y ∧ Tendsto (fun n => f (σ n) z) atTop (𝓝 y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨id, strictMono_id, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨φ, hφ, hprev⟩ := ih
      obtain ⟨z, y, ψ, hψ, hR, hlim⟩ := hselect φ hφ i
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨z, y, hR, hlim⟩
      · obtain ⟨z', y', hR', hlim'⟩ := hprev j hj
        exact ⟨z', y', hR', hlim'.comp hψ.tendsto_atTop⟩
  obtain ⟨σ, hσ, hlim⟩ := hfin Finset.univ
  exact ⟨σ, hσ, fun i => hlim i (Finset.mem_univ i)⟩

end VeechDichotomy.FiniteSimultaneousLimits
