module

public import VeechDichotomy.HyperbolicDirichletInterior

/-! The actual corner/elliptic vertex-candidate set is closed and
discrete in the genuine hyperbolic plane. The proof derives these
topological facts from the already proved finite intersections with
compact sets, rather than assuming isolated vertices. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicVertexLocalDiscreteness

open Set Filter Topology

section General

variable {X : Type*} [TopologicalSpace X] [T1Space X] [WeaklyLocallyCompactSpace X]

theorem closed_of_compact_finite (S : Set X)
    (hfinite : ∀ K : Set X, IsCompact K → (S ∩ K).Finite) : IsClosed S := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds z
  have hf := hfinite K hK
  have hn : (S ∩ K)ᶜ ∈ 𝓝 z := hf.isClosed.isOpen_compl.mem_nhds (fun h => hz h.1)
  apply Filter.mem_of_superset (inter_mem hKn hn)
  intro w hw hwS
  exact hw.2 ⟨hwS, hw.1⟩

theorem discrete_of_compact_finite (S : Set X)
    (hfinite : ∀ K : Set X, IsCompact K → (S ∩ K).Finite) : IsDiscrete S := by
  apply isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro z
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds z.val
  let F := (S ∩ K) \ {z.val}
  have hf : F.Finite := (hfinite K hK).sdiff
  have hzF : z.val ∉ F := fun h => h.2 rfl
  have hn : K ∩ Fᶜ ∈ 𝓝 z.val := inter_mem hKn (hf.isClosed.isOpen_compl.mem_nhds hzF)
  have hpre := (continuous_subtype_val : Continuous (Subtype.val : S → X)).continuousAt hn
  have hsub : (Subtype.val : S → X) ⁻¹' (K ∩ Fᶜ) ⊆ ({z} : Set S) := by
    intro w hw
    change w = z
    apply Subtype.ext
    by_contra hneq
    exact hw.2 ⟨⟨w.property, hw.1⟩, hneq⟩
  have hsingle : ({z} : Set S) ∈ 𝓝 z := Filter.mem_of_superset hpre hsub
  apply isOpen_iff_mem_nhds.mpr
  rintro _ rfl
  exact hsingle

end General

open LinearGroup HyperbolicEllipticLocalFiniteness HyperbolicRegularCenters HyperbolicDirichletRegions
open scoped UpperHalfPlane

theorem vertexCandidates_closed (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) :
    IsClosed (vertexCandidates Γ p) :=
  closed_of_compact_finite _ (fun _ hK => vertexCandidates_finite_inter_compact Γ p hK)

theorem vertexCandidates_discrete (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) :
    IsDiscrete (vertexCandidates Γ p) :=
  discrete_of_compact_finite _ (fun _ hK => vertexCandidates_finite_inter_compact Γ p hK)

theorem boundary_vertex_data (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) (hp : RegularCenter Γ p) :
    IsClosed (vertexCandidates Γ p) ∧ IsDiscrete (vertexCandidates Γ p) ∧
      vertexCandidates Γ p ⊆ frontier (region Γ p) :=
  ⟨vertexCandidates_closed Γ p, vertexCandidates_discrete Γ p,
    HyperbolicDirichletInterior.vertexCandidates_subset_frontier Γ p hp⟩

end VeechDichotomy.HyperbolicVertexLocalDiscreteness
