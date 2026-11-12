module

public import MNEC.CutBankLifts

@[expose] public section

/-!
# The image of an actual half-collar

The continuous bank lift covers exactly the bank neighborhood used to
generate the cut topology. This is proved from the explicit coordinate
formulas, not supplied as a field in collar data.
-/

noncomputable section

namespace MNEC.HalfCollarRanges

open LatticeTorus CutTorus OffSlitEmbeddings SlitCollars CutBankLifts Set

theorem halfLift_mem_bankNeighborhood {L : Lattice} {w : Plane}
    (C : Collar L w) (k : Bool) (q : HalfDomain C) :
    halfLift C k q ∈ bankNeighborhood L w C.a C.b C.r k := by
  by_cases hq : q.val.2 = 0
  · rw [halfLift_zero C k q hq]
    exact Or.inr ⟨rfl, q.val.1, q.property.1.1, rfl⟩
  · apply Or.inl
    refine ⟨?_, q.val.1, q.property.1.1, q.val.2, ?_, ?_⟩
    · rw [base_halfLift]
      exact halfBase_off_slit C k q hq
    · exact ⟨lt_of_le_of_ne q.property.2 (Ne.symm hq), q.property.1.2.2⟩
    · rw [base_halfLift]
      rfl

theorem exists_halfLift_of_mem_bankNeighborhood {L : Lattice} {w : Plane}
    (C : Collar L w) (k : Bool) (p : Point L w)
    (hp : p ∈ bankNeighborhood L w C.a C.b C.r k) :
    ∃ q : HalfDomain C, halfLift C k q = p := by
  rcases hp with ⟨hoff, s, hs, t, ht, heq⟩ | ⟨hbank, s, hs, heq⟩
  · let q : HalfDomain C := ⟨(s, t),
      ⟨⟨hs, ⟨(neg_lt_zero.mpr C.r_pos).trans ht.1, ht.2⟩⟩, ht.1.le⟩⟩
    have hq : q.val.2 ≠ 0 := ht.1.ne'
    refine ⟨q, ?_⟩
    rw [halfLift_nonzero C k q hq]
    apply point_ext
    · exact heq
    · exact (bank_false_off_interior p (fun hi => hoff (interior_subset_slit L w hi))).symm
  · let q : HalfDomain C := ⟨(s, 0), ⟨⟨hs, ⟨neg_lt_zero.mpr C.r_pos, C.r_pos⟩⟩, le_rfl⟩⟩
    refine ⟨q, ?_⟩
    rw [halfLift_zero C k q rfl]
    exact point_ext heq hbank.symm

theorem range_halfLift {L : Lattice} {w : Plane}
    (C : Collar L w) (k : Bool) :
    range (halfLift C k) = bankNeighborhood L w C.a C.b C.r k := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, rfl⟩
    exact halfLift_mem_bankNeighborhood C k q
  · intro p hp
    exact exists_halfLift_of_mem_bankNeighborhood C k p hp

end MNEC.HalfCollarRanges
