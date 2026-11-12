module

public import VeechDichotomy.CompactReturnNondivergence
public import VeechDichotomy.CompactLift
public import Mathlib.Tactic.Group

/-! A ray contracting a genuine nonidentity lattice element diverges
in the actual discrete subgroup quotient. Compact representatives turn
the contracting conjugates into nonidentity subgroup elements uniformly
near the identity, contradicting discreteness. No finite-volume or cusp
classification assumption is needed for this direction. -/

@[expose] public section

namespace VeechDichotomy.DiscreteQuotientContraction

open Set Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem eventually_identity (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∀ᶠ z in 𝓝 (1 : G), z ∈ Γ → z = 1 := by
  have hone : ({1} : Set Γ) ∈ 𝓝 (1 : Γ) := (isOpen_discrete _).mem_nhds (by simp)
  rw [nhds_subtype_eq_comap] at hone
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hone
  filter_upwards [hU] with z hz hzΓ
  have heq : (⟨z, hzΓ⟩ : Γ) = 1 := hsub hz
  exact congrArg Subtype.val heq

theorem uniformly_identity (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) :
    ∀ᶠ z in 𝓝 (1 : G), ∀ b ∈ K, b⁻¹ * z * b ∈ Γ → b⁻¹ * z * b = 1 := by
  apply hK.eventually_forall_of_forall_eventually
  intro b _
  have hc : Continuous (fun p : G × G => p.2⁻¹ * p.1 * p.2) := by fun_prop
  have hlim : Tendsto (fun p : G × G => p.2⁻¹ * p.1 * p.2) (𝓝 (1, b)) (𝓝 (1 : G)) := by
    simpa using hc.continuousAt.tendsto (x := (1, b))
  exact hlim (eventually_identity Γ)

variable [WeaklyLocallyCompactSpace G]

theorem not_hasCompactReturns (Γ : Subgroup G) [DiscreteTopology Γ]
    (a : ℝ → G) {γ : G} (hγ : γ ∈ Γ) (hne : γ ≠ 1)
    (hcontract : Tendsto (fun t => a t * γ * (a t)⁻¹) atTop (𝓝 (1 : G))) :
    ¬ HasCompactReturns (fun t => (QuotientGroup.mk (a t) : G ⧸ Γ)) := by
  rintro ⟨C, hC, hfreq⟩
  obtain ⟨K, hK, hnormal⟩ := exists_compact_right_normalizers Γ hC
  have hsmall := hcontract (uniformly_identity Γ hK)
  obtain ⟨t, htC, ht⟩ := (hfreq.and_eventually hsmall).exists
  obtain ⟨δ, hδ⟩ := hnormal (a t) htC
  have hform : (a t * (δ : G))⁻¹ * (a t * γ * (a t)⁻¹) * (a t * (δ : G)) =
      (δ : G)⁻¹ * γ * (δ : G) := by group
  have hm : (a t * (δ : G))⁻¹ * (a t * γ * (a t)⁻¹) * (a t * (δ : G)) ∈ Γ := by
    rw [hform]
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem δ.property) hγ) δ.property
  have heq : (δ : G)⁻¹ * γ * (δ : G) = 1 := hform.symm.trans (ht _ hδ hm)
  apply hne
  calc
    γ = (δ : G) * ((δ : G)⁻¹ * γ * (δ : G)) * (δ : G)⁻¹ := by group
    _ = 1 := by rw [heq]; group

theorem divergent (Γ : Subgroup G) [DiscreteTopology Γ]
    (a : ℝ → G) {γ : G} (hγ : γ ∈ Γ) (hne : γ ≠ 1)
    (hcontract : Tendsto (fun t => a t * γ * (a t)⁻¹) atTop (𝓝 (1 : G))) :
    Tendsto (fun t => (QuotientGroup.mk (a t) : G ⧸ Γ)) atTop (cocompact (G ⧸ Γ)) := by
  by_contra h
  exact not_hasCompactReturns Γ a hγ hne hcontract ((hasCompactReturns_iff_not_divergent _).mpr h)

end VeechDichotomy.DiscreteQuotientContraction
