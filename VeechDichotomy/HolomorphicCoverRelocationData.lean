module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Complex.Basic

/-! Inputs for a general source-atlas gluing construction. They are
ordinary hypotheses of the construction; the marked native cover will
instantiate every one from its proved maps, regions and local inverses. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HolomorphicCoverRelocationData

open Set Filter Topology
open scoped Manifold ContDiff

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E N]

structure Data where
  map : M → N
  holomorphic : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω map
  transport : N ≃ₜ N
  region : Set N
  region_open : IsOpen region
  transport_holomorphic : ∀ x ∈ region, ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω transport x
  inverse_holomorphic : ∀ x ∈ region, ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω transport.symm (transport x)
  critical : Set M
  critical_region : ∀ x ∈ critical, map x ∈ region
  localMap : ↥(criticalᶜ) → OpenPartialHomeomorph M N
  local_center : ∀ x, x.val ∈ (localMap x).source
  local_apply : ∀ x z, localMap x z = map z
  local_inverse : ∀ x z, z ∈ (localMap x).target → ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (localMap x).symm z

namespace Data

variable (A : Data (E := E) (M := M) (N := N))

def sourceRegion : Set M := A.map ⁻¹' A.region

theorem sourceRegion_open : IsOpen A.sourceRegion := A.region_open.preimage A.holomorphic.continuous

def criticalChart (x : M) : OpenPartialHomeomorph M E := (chartAt E x).restr A.sourceRegion

def targetChart (x : ↥(A.criticalᶜ)) : OpenPartialHomeomorph N E := chartAt E (A.transport (A.map x.val))

def regularChart (x : ↥(A.criticalᶜ)) : OpenPartialHomeomorph M E :=
  ((A.localMap x).transHomeomorph A.transport).trans (A.targetChart x)

theorem regular_apply (x : ↥(A.criticalᶜ)) (z : M) : A.regularChart x z = A.targetChart x (A.transport (A.map z)) := by
  change A.targetChart x (A.transport (A.localMap x z)) = _
  rw [A.local_apply]

theorem regular_source (x : ↥(A.criticalᶜ)) (z : M) : z ∈ (A.regularChart x).source ↔
    z ∈ (A.localMap x).source ∧ A.transport (A.map z) ∈ (A.targetChart x).source := by
  change (z ∈ (A.localMap x).source ∧ A.transport (A.localMap x z) ∈ (A.targetChart x).source) ↔ _
  rw [A.local_apply]

theorem regular_target (x : ↥(A.criticalᶜ)) (z : E) : z ∈ (A.regularChart x).target ↔
    z ∈ (A.targetChart x).target ∧ A.transport.symm ((A.targetChart x).symm z) ∈ (A.localMap x).target := Iff.rfl

theorem regular_inverse_projection (x : ↥(A.criticalᶜ)) {z : E} (hz : z ∈ (A.regularChart x).target) :
    A.transport (A.map ((A.regularChart x).symm z)) = (A.targetChart x).symm z := by
  have ht := (A.regular_target x z).mp hz
  have h := (A.localMap x).right_inv ht.2
  rw [A.local_apply] at h
  exact (congrArg A.transport h).trans (A.transport.apply_symm_apply _)

theorem critical_center {x : M} (hx : x ∈ A.critical) : x ∈ (A.criticalChart x).source := by
  refine ⟨mem_chart_source E x, ?_⟩
  rw [A.sourceRegion_open.interior_eq]
  exact A.critical_region x hx

theorem regular_center (x : ↥(A.criticalᶜ)) : x.val ∈ (A.regularChart x).source := by
  rw [A.regular_source]
  exact ⟨A.local_center x, mem_chart_source E (A.transport (A.map x.val))⟩

end Data
end VeechDichotomy.HolomorphicCoverRelocationData
