module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Sequences

/-! A convergent sequence of parameters in a proper family gives
actual subsequential limits in the exact limit fiber. Frequently
visited closed sets retain a limit point in that set. -/

@[expose] public section

namespace VeechDichotomy.ProperFiberLimits

open Set Filter Topology

variable {T P : Type*} [TopologicalSpace T] [FirstCountableTopology T]
  [TopologicalSpace P] [T2Space P]

theorem subsequence_in_closed (π : T → P) (hπ : IsProperMap π)
    (x : ℕ → T) (p₀ : P) (hp : Tendsto (fun n => π (x n)) atTop (𝓝 p₀))
    {C : Set T} (hC : IsClosed C) (hfreq : ∃ᶠ n in atTop, x n ∈ C) :
    ∃ y ∈ C, π y = p₀ ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (x ∘ σ) atTop (𝓝 y) := by
  let K := π ⁻¹' insert p₀ (range (fun n => π (x n)))
  have hK : IsCompact K := hπ.isCompact_preimage hp.isCompact_insert_range
  have hxK : ∀ n, x n ∈ K := fun n => mem_insert_of_mem p₀ ⟨n, rfl⟩
  have hfreqKC : ∃ᶠ n in atTop, x n ∈ K ∩ C := hfreq.mono (fun n hn => ⟨hxK n, hn⟩)
  obtain ⟨y, hy, σ, hσ, hlim⟩ := (hK.inter_right hC).tendsto_subseq' hfreqKC
  have hproj : Tendsto (fun n => π (x (σ n))) atTop (𝓝 (π y)) :=
    hπ.continuous.continuousAt.tendsto.comp hlim
  have hsame : π y = p₀ := tendsto_nhds_unique hproj (hp.comp hσ.tendsto_atTop)
  exact ⟨y, hy.2, hsame, σ, hσ, hlim⟩

theorem subsequence (π : T → P) (hπ : IsProperMap π)
    (x : ℕ → T) (p₀ : P) (hp : Tendsto (fun n => π (x n)) atTop (𝓝 p₀)) :
    ∃ y, π y = p₀ ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (x ∘ σ) atTop (𝓝 y) := by
  obtain ⟨y, _, hy, σ, hσ, hlim⟩ := subsequence_in_closed π hπ x p₀ hp isClosed_univ
    (Frequently.of_forall (fun _ => mem_univ _))
  exact ⟨y, hy, σ, hσ, hlim⟩

end VeechDichotomy.ProperFiberLimits
