module

public import Mathlib.Topology.Sequences
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Interval.Finset.Basic

/-! A sequence in a compact first-countable space, with finitely many
labels, has a convergent subsequence with one constant label. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CompactFiniteLabels

open Set Filter Topology

theorem constant_subsequence {B : Type*} [Finite B] (label : ℕ → B) :
    ∃ j : B, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, label (σ n) = j := by
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber label
  have hInfinite : (label ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
  obtain ⟨τ, hτ, hlabel⟩ := Nat.exists_strictMono_subsequence (P := fun n => label n = j) (fun N => by
    obtain ⟨n, hn, hN⟩ := hInfinite.exists_gt N
    exact ⟨n, hN, hn⟩)
  exact ⟨j, τ, hτ, hlabel⟩

theorem subsequence {P B : Type*} [TopologicalSpace P] [FirstCountableTopology P] [Finite B]
    {K : Set P} (hK : IsCompact K) (a : ℕ → P) (ha : ∀ n, a n ∈ K) (label : ℕ → B) :
    ∃ j : B, ∃ p ∈ K, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 p) ∧
      ∀ n, label (σ n) = j := by
  obtain ⟨j, τ, hτ, hlabel⟩ := constant_subsequence label
  obtain ⟨p, hp, υ, hυ, hconv⟩ := hK.tendsto_subseq (fun n => ha (τ n))
  exact ⟨j, p, hp, τ ∘ υ, hτ.comp hυ, hconv, fun n => hlabel (υ n)⟩

end VeechDichotomy.CompactFiniteLabels
