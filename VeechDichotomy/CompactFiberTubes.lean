module

public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Compact subsets of a slice of an open product persist on nearby
slices. Joint continuity gives uniform convergence on those subsets,
without a choice of charts depending on the varying parameter. -/

@[expose] public section

namespace VeechDichotomy.CompactFiberTubes

open Set Filter Topology
open scoped Uniformity

variable {P Z W : Type*} [TopologicalSpace P] [TopologicalSpace Z]

theorem exists_open_tube {D : Set (P × Z)} (hD : IsOpen D) (a : P)
    {K : Set Z} (hK : IsCompact K) (hsub : ∀ z ∈ K, (a, z) ∈ D) :
    ∃ U : Set P, IsOpen U ∧ a ∈ U ∧ ∀ p ∈ U, ∀ z ∈ K, (p, z) ∈ D := by
  have hprod : ({a} : Set P) ×ˢ K ⊆ D := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    rcases mem_singleton_iff.mp hp with rfl
    exact hsub z hz
  obtain ⟨U, V, hU, _, haU, hKV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK hD hprod
  exact ⟨U, hU, haU (mem_singleton a), fun p hp z hz => hUV ⟨hp, hKV hz⟩⟩

theorem tendstoUniformlyOn [UniformSpace W] {D : Set (P × Z)} (hD : IsOpen D)
    {f : P × Z → W} (hf : ContinuousOn f D) (a : P)
    {K : Set Z} (hK : IsCompact K) (hsub : ∀ z ∈ K, (a, z) ∈ D) :
    TendstoUniformlyOn (fun p z => f (p, z)) (fun z => f (a, z)) (𝓝 a) K := by
  obtain ⟨U, hU, haU, hUD⟩ := exists_open_tube hD a hK hsub
  have hcont : ContinuousOn (fun p : P × Z => f (p.1, p.2)) (U ×ˢ K) :=
    hf.mono (fun p hp => hUD p.1 hp.1 p.2 hp.2)
  intro u hu
  obtain ⟨V, hV, hv⟩ := hK.mem_uniformity_of_prod (f := fun p z => f (p, z))
    hcont haU (symmetrize_mem_uniformity hu)
  rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds haU)] at hV
  filter_upwards [hV] with p hp
  intro z hz
  exact (hv p hp z hz).2

end VeechDichotomy.CompactFiberTubes
