module

public import Mathlib.Topology.Connected.Basic

/-! A preconnected set covered by open sets that are either equal
or disjoint lies in one member of the family as soon as it meets it.
The family may be infinite and may contain repeated sets. -/

@[expose] public section

namespace VeechDichotomy.ConnectedOpenFamilies

open Set

theorem subset_one {X I : Type*} [TopologicalSpace X] (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hpair : ∀ i j, U i = U j ∨ Disjoint (U i) (U j))
    {S : Set X} (hS : IsPreconnected S) (hcover : S ⊆ ⋃ i, U i) (j : I) (hne : (S ∩ U j).Nonempty) :
    S ⊆ U j := by
  classical
  let V : Set X := ⋃ i : {i : I | U i ≠ U j}, U i.val
  have hV : IsOpen V := isOpen_iUnion (fun i => hopen i.val)
  have hd : Disjoint (U j) V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxV
    rcases hpair i.val j with he | hdisj
    · exact i.property he
    · exact Set.disjoint_left.mp hdisj hi hx
  have hsub : S ⊆ U j ∪ V := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    by_cases he : U i = U j
    · exact Or.inl (he ▸ hi)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i, he⟩, hi⟩)
  exact hS.subset_left_of_subset_union (hopen j) hV hd hsub hne

theorem exists_container {X I : Type*} [TopologicalSpace X] (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hpair : ∀ i j, U i = U j ∨ Disjoint (U i) (U j))
    {S : Set X} (hS : IsPreconnected S) (hne : S.Nonempty) (hcover : S ⊆ ⋃ i, U i) :
    ∃ j : I, S ⊆ U j := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
  exact ⟨j, subset_one U hopen hpair hS hcover j ⟨x, hx, hj⟩⟩

end VeechDichotomy.ConnectedOpenFamilies
