module

public import MNEC.CutBankLifts

@[expose] public section

/-!
# Open two-sided neighborhoods of the seam

The two banks are an explicit saturated open subset of the actual cut
sum. Openness is proved from the quotient topology and the generators of
the cut topology, rather than assumed as a property of a proposed chart.
-/

noncomputable section

namespace MNEC.SeamOpenSets

open LatticeTorus CutTorus SlitConnectedSum SlitCollars CutBankLifts Set Topology
open scoped Classical

theorem endpoint_not_mem_bankNeighborhood (L : Lattice) (w : Plane)
    (hw : L.EmbeddedSlit w) (a b r : ℝ) (k : Bool)
    (ha : 0 < a) (hb : b < 1) (p : Point L w) (hp : base p ∈ endpoints L w) :
    p ∉ bankNeighborhood L w a b r k := by
  intro h
  rcases h with ⟨hnot, _⟩ | ⟨_, s, hs, heq⟩
  · exact hnot (endpoints_subset_slit L w hp)
  · have hi : base p ∈ interior L w :=
      ⟨s, ha.trans hs.1, hs.2.trans hb, heq⟩
    exact Set.disjoint_left.mp (interior_disjoint_endpoints L w hw) hi hp

def rawNeighborhood {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (k : Bool) : Set (Raw L₁ L₂ w) :=
  Sum.inl '' bankNeighborhood L₁ w C.a C.b C.r k ∪
    Sum.inr '' bankNeighborhood L₂ w C.a C.b C.r (!k)

@[simp] theorem mem_rawNeighborhood_inl {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Point L₁ w) :
    Sum.inl p ∈ rawNeighborhood C k ↔ p ∈ bankNeighborhood L₁ w C.a C.b C.r k := by
  simp [rawNeighborhood]

@[simp] theorem mem_rawNeighborhood_inr {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Point L₂ w) :
    Sum.inr p ∈ rawNeighborhood C k ↔ p ∈ bankNeighborhood L₂ w C.a C.b C.r (!k) := by
  simp [rawNeighborhood]

theorem rawNeighborhood_open {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) : IsOpen (rawNeighborhood C k) :=
  (isOpenMap_inl _ (bankNeighborhood_open L₁ w C.a C.b C.r k
    C.a_pos C.a_lt_b C.b_lt_one C.r_pos)).union
    (isOpenMap_inr _ (bankNeighborhood_open L₂ w C.a C.b C.r (!k)
      C.a_pos C.a_lt_b C.b_lt_one C.r_pos))

theorem mem_rawNeighborhood_seam {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) {p q : Raw L₁ L₂ w}
    (hpq : SeamRelation L₁ L₂ w p q) :
    p ∈ rawNeighborhood C k ↔ q ∈ rawNeighborhood C k := by
  cases hpq with
  | upper_lower t ht ht' =>
      rw [mem_rawNeighborhood_inl, mem_rawNeighborhood_inr]
      change interiorBank L₁ w false t ⟨ht, ht'⟩ ∈ bankNeighborhood L₁ w C.a C.b C.r k ↔
        interiorBank L₂ w true t ⟨ht, ht'⟩ ∈ bankNeighborhood L₂ w C.a C.b C.r (!k)
      rw [mem_bankNeighborhood_interiorBank L₁ w hw₁ false k C.a C.b C.r t
        C.a_pos C.b_lt_one ⟨ht, ht'⟩,
        mem_bankNeighborhood_interiorBank L₂ w hw₂ true (!k) C.a C.b C.r t
        C.a_pos C.b_lt_one ⟨ht, ht'⟩]
      cases k <;> simp
  | lower_upper t ht ht' =>
      rw [mem_rawNeighborhood_inl, mem_rawNeighborhood_inr]
      change interiorBank L₁ w true t ⟨ht, ht'⟩ ∈ bankNeighborhood L₁ w C.a C.b C.r k ↔
        interiorBank L₂ w false t ⟨ht, ht'⟩ ∈ bankNeighborhood L₂ w C.a C.b C.r (!k)
      rw [mem_bankNeighborhood_interiorBank L₁ w hw₁ true k C.a C.b C.r t
        C.a_pos C.b_lt_one ⟨ht, ht'⟩,
        mem_bankNeighborhood_interiorBank L₂ w hw₂ false (!k) C.a C.b C.r t
        C.a_pos C.b_lt_one ⟨ht, ht'⟩]
      cases k <;> simp
  | initial =>
      rw [mem_rawNeighborhood_inl, mem_rawNeighborhood_inr]
      exact iff_of_false
        (endpoint_not_mem_bankNeighborhood L₁ w hw₁ C.a C.b C.r k C.a_pos C.b_lt_one
          _ (Or.inl rfl))
        (endpoint_not_mem_bankNeighborhood L₂ w hw₂ C.a C.b C.r (!k) C.a_pos C.b_lt_one
          _ (Or.inl rfl))
  | terminal =>
      rw [mem_rawNeighborhood_inl, mem_rawNeighborhood_inr]
      exact iff_of_false
        (endpoint_not_mem_bankNeighborhood L₁ w hw₁ C.a C.b C.r k C.a_pos C.b_lt_one
          _ (Or.inr (Set.mem_singleton _)))
        (endpoint_not_mem_bankNeighborhood L₂ w hw₂ C.a C.b C.r (!k) C.a_pos C.b_lt_one
          _ (Or.inr (Set.mem_singleton _)))

theorem mem_rawNeighborhood_related {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) {p q : Raw L₁ L₂ w}
    (hpq : Relation.EqvGen (SeamRelation L₁ L₂ w) p q) :
    p ∈ rawNeighborhood C k ↔ q ∈ rawNeighborhood C k := by
  induction hpq with
  | rel _ _ h => exact mem_rawNeighborhood_seam hw₁ hw₂ C k h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem preimage_image_rawNeighborhood {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    glue L₁ L₂ w ⁻¹' (glue L₁ L₂ w '' rawNeighborhood C k) = rawNeighborhood C k := by
  ext p
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (mem_rawNeighborhood_related hw₁ hw₂ C k (Quotient.exact heq)).mp hq
  · exact fun hp => ⟨p, hp, rfl⟩

def seamNeighborhood {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) : Set (Surface L₁ L₂ w) :=
  glue L₁ L₂ w '' rawNeighborhood C k

theorem seamNeighborhood_open {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : IsOpen (seamNeighborhood C k) := by
  have hpre : IsOpen (glue L₁ L₂ w ⁻¹' seamNeighborhood C k) := by
    rw [seamNeighborhood, preimage_image_rawNeighborhood hw₁ hw₂ C k]
    exact rawNeighborhood_open C k
  exact (isQuotientMap_quotient_mk' (s := gluingSetoid L₁ L₂ w)).isCoinducing.isOpen_preimage.mp hpre

end MNEC.SeamOpenSets
