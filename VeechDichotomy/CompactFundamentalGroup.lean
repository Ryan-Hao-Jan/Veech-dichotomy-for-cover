module

public import VeechDichotomy.CompactCoreLoopGenerators

/-! Finite generation of the actual fundamental group from a compact
core carrying all based loop classes. The compact-space case follows
without a compact-core hypothesis. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CompactFundamentalGroup

open Set Topology Path.Homotopic.Quotient

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [PseudoMetricSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]

theorem fg_of_compact_core {K : Set X} (hK : IsCompact K) {o : X} (ho : o ∈ K)
    (hlocal : ∀ x ∈ K, ∃ U : Set X, U ∈ nhds x ∧ IsSimplyConnected U)
    (hcore : ∀ γ : Path o o, ∃ η : Path o o, range η ⊆ K ∧ γ.Homotopic η) :
    Group.FG (FundamentalGroup X o) := by
  obtain ⟨S, hS, hgen⟩ := CompactCoreLoopGenerators.exists_generators hK ho hlocal
  apply Group.fg_iff.mpr
  refine ⟨S, ?_, hS⟩
  apply top_unique
  intro g _
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep g.asHom
  obtain ⟨η, hηK, hγη⟩ := hcore γ
  have hmem := hgen η hηK
  have hpath : mk γ = mk η := Path.Homotopic.Quotient.eq.mpr hγη
  have heq : FundamentalGroup.fromPath (mk η) = g := by
    apply CategoryTheory.End.ext
    exact hpath.symm.trans hγ
  rwa [heq] at hmem

theorem fg_of_compact [CompactSpace X] (o : X)
    (hlocal : ∀ x, ∃ U : Set X, U ∈ nhds x ∧ IsSimplyConnected U) :
    Group.FG (FundamentalGroup X o) :=
  fg_of_compact_core isCompact_univ (mem_univ o) (fun x _ => hlocal x)
    (fun γ => ⟨γ, subset_univ _, Path.Homotopic.refl γ⟩)

end VeechDichotomy.CompactFundamentalGroup
