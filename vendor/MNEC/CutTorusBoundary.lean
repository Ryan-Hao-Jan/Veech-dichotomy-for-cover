module

public import MNEC.CutBankLifts
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

/-!
# Boundary arcs and Hausdorff separation in the actual cut torus

The two closed-interval arcs use the specified bank in the interior and the
unique endpoint lift. Their continuity is checked on the generators of the
cut topology. Constructed physical collars separate opposite banks, proving
Hausdorffness rather than installing it as an assumption.
-/

noncomputable section

namespace MNEC.CutTorusBoundary

open LatticeTorus CutTorus OffSlitEmbeddings SlitCollars CutBankLifts Set Topology
open scoped Classical

def boundaryArc (L : Lattice) (w : Plane) (k : Bool) (t : Parameter) : Point L w :=
  ⟨(L.arc w t, if 0 < (t : ℝ) ∧ (t : ℝ) < 1 then k else false), by
    by_cases ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1
    · exact Or.inr ⟨t, ht.1, ht.2, rfl⟩
    · exact Or.inl (ite_eq_right ht)⟩

@[simp] theorem base_boundaryArc (L : Lattice) (w : Plane) (k : Bool) (t : Parameter) :
    base (boundaryArc L w k t) = L.arc w t := rfl

theorem bank_boundaryArc_interior (L : Lattice) (w : Plane) (k : Bool) (t : Parameter)
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) : bank (boundaryArc L w k t) = k :=
  ite_eq_left ht

theorem boundaryArc_zero (L : Lattice) (w : Plane) (k : Bool) :
    boundaryArc L w k ⟨0, by constructor <;> norm_num⟩ = upper L w (L.project 0) := by
  apply point_ext
  · simp [Lattice.arc]
  · change (if 0 < (0 : ℝ) ∧ (0 : ℝ) < 1 then k else false) = false
    simp

theorem boundaryArc_one (L : Lattice) (w : Plane) (k : Bool) :
    boundaryArc L w k ⟨1, by constructor <;> norm_num⟩ = upper L w (L.project w) := by
  apply point_ext
  · simp [Lattice.arc]
  · change (if 0 < (1 : ℝ) ∧ (1 : ℝ) < 1 then k else false) = false
    simp

theorem boundaryArc_false (L : Lattice) (w : Plane) (t : Parameter) :
    boundaryArc L w false t = upper L w (L.arc w t) := by
  apply point_ext (p := boundaryArc L w false t) (q := upper L w (L.arc w t)) rfl
  change (if 0 < (t : ℝ) ∧ (t : ℝ) < 1 then false else false) = false
  split <;> rfl

theorem boundaryArc_interior (L : Lattice) (w : Plane) (k : Bool) (t : Parameter)
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1) :
    boundaryArc L w k t = interiorBank L w k t ht := by
  apply point_ext (p := boundaryArc L w k t) (q := interiorBank L w k t ht) rfl
  exact bank_boundaryArc_interior L w k t ht

theorem mem_bankNeighborhood_boundaryArc (L : Lattice) (w : Plane)
    (hw : L.EmbeddedSlit w) (k l : Bool) (a b r : ℝ)
    (ha : 0 < a) (hb : b < 1) (t : Parameter) :
    boundaryArc L w k t ∈ bankNeighborhood L w a b r l ↔
      (t : ℝ) ∈ Ioo a b ∧ k = l := by
  constructor
  · intro hmem
    rcases hmem with ⟨hnot, _⟩ | ⟨hbank, s, hs, heq⟩
    · exact False.elim (hnot ⟨t, rfl⟩)
    · have hsi : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(ha.trans hs.1).le, (hs.2.trans hb).le⟩
      have hst : s = (t : ℝ) := congrArg Subtype.val
        (hw (show L.arc w ⟨s, hsi⟩ = L.arc w t from heq))
      have ht : (t : ℝ) ∈ Ioo a b := hst ▸ hs
      have hint : 0 < (t : ℝ) ∧ (t : ℝ) < 1 := ⟨ha.trans ht.1, ht.2.trans hb⟩
      rw [bank_boundaryArc_interior L w k t hint] at hbank
      exact ⟨ht, hbank⟩
  · rintro ⟨ht, hkl⟩
    have hint : 0 < (t : ℝ) ∧ (t : ℝ) < 1 := ⟨ha.trans ht.1, ht.2.trans hb⟩
    exact Or.inr ⟨(bank_boundaryArc_interior L w k t hint).trans hkl, t, ht, rfl⟩

theorem continuous_boundaryArc (L : Lattice) (w : Plane)
    (hw : L.EmbeddedSlit w) (k : Bool) : Continuous (boundaryArc L w k) := by
  apply continuous_generateFrom_iff.mpr
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩ | ⟨a, b, r, l, ha, _hab, hb, _hr, rfl⟩
  · have heq : boundaryArc L w k ⁻¹' (base ⁻¹' V) = L.arc w ⁻¹' V := rfl
    rw [heq]
    exact hV.preimage (L.continuous_arc w)
  · by_cases hkl : k = l
    · have heq : boundaryArc L w k ⁻¹' bankNeighborhood L w a b r l =
          (fun t : Parameter => (t : ℝ)) ⁻¹' Ioo a b := by
        ext t
        change boundaryArc L w k t ∈ bankNeighborhood L w a b r l ↔ (t : ℝ) ∈ Ioo a b
        rw [mem_bankNeighborhood_boundaryArc L w hw k l a b r ha hb]
        exact and_iff_left hkl
      rw [heq]
      exact isOpen_Ioo.preimage continuous_subtype_val
    · have heq : boundaryArc L w k ⁻¹' bankNeighborhood L w a b r l = ∅ := by
        ext t
        change (boundaryArc L w k t ∈ bankNeighborhood L w a b r l) ↔ False
        rw [mem_bankNeighborhood_boundaryArc L w hw k l a b r ha hb]
        simp only [hkl, and_false]
      rw [heq]
      exact isOpen_empty

theorem boundaryArc_injective (L : Lattice) (w : Plane)
    (hw : L.EmbeddedSlit w) (k : Bool) : Function.Injective (boundaryArc L w k) := by
  intro s t h
  exact hw (congrArg base h)

def boundarySet (L : Lattice) (w : Plane) : Set (Point L w) := base ⁻¹' L.slitSet w

theorem boundaryArc_of_base_on_arc (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w)
    (q : Point L w) (t : Parameter) (hbase : base q = L.arc w t) :
    boundaryArc L w (bank q) t = q := by
  apply point_ext (p := boundaryArc L w (bank q) t) (q := q) hbase.symm
  by_cases ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1
  · exact bank_boundaryArc_interior L w (bank q) t ht
  · have hnot : base q ∉ interior L w := by
      rintro ⟨s, hs, hs1, heq⟩
      have hst : s = (t : ℝ) := congrArg Subtype.val
        (hw (show L.arc w ⟨s, hs.le, hs1.le⟩ = L.arc w t from heq.trans hbase))
      exact ht (hst ▸ ⟨hs, hs1⟩)
    have hb := bank_false_off_interior q hnot
    change (if 0 < (t : ℝ) ∧ (t : ℝ) < 1 then bank q else false) = bank q
    rw [ite_eq_right ht, hb]

theorem boundarySet_eq_union_ranges (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w) :
    boundarySet L w = range (boundaryArc L w false) ∪ range (boundaryArc L w true) := by
  ext q
  constructor
  · rintro ⟨t, ht⟩
    have heq := boundaryArc_of_base_on_arc L w hw q t ht.symm
    cases hk : bank q
    · exact Or.inl ⟨t, by simpa only [hk] using heq⟩
    · exact Or.inr ⟨t, by simpa only [hk] using heq⟩
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> exact ⟨t, rfl⟩

theorem boundarySet_compact (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w) :
    IsCompact (boundarySet L w) := by
  rw [boundarySet_eq_union_ranges L w hw]
  exact (isCompact_range (continuous_boundaryArc L w hw false)).union
    (isCompact_range (continuous_boundaryArc L w hw true))

theorem boundarySet_closed (L : Lattice) (w : Plane) : IsClosed (boundarySet L w) :=
  (L.slitSet_closed w).preimage (continuous_base L w)

theorem projected_axis_mem_slit {L : Lattice} {w : Plane} (C : Collar L w)
    (s : ℝ) (hs : s ∈ Ioo C.a C.b) : L.project (s • w) ∈ L.slitSet w :=
  ⟨⟨s, (C.a_pos.trans hs.1).le, (hs.2.trans C.b_lt_one).le⟩, rfl⟩

theorem bankNeighborhoods_disjoint {L : Lattice} {w : Plane} (C : Collar L w) :
    Disjoint (bankNeighborhood L w C.a C.b C.r false)
      (bankNeighborhood L w C.a C.b C.r true) := by
  apply Set.disjoint_left.mpr
  intro q hp hm
  rcases hp with ⟨hpoff, s, hs, t, ht, hpp⟩ | ⟨hpb, s, hs, hpp⟩
  · rcases hm with ⟨_, s', hs', t', ht', hmp⟩ | ⟨_, s', hs', hmp⟩
    · have hplus : ((s, t) : Plane) ∈ domain C :=
        ⟨hs, ⟨by linarith only [ht.1, C.r_pos], ht.2⟩⟩
      have hminus : ((s', -t') : Plane) ∈ domain C :=
        ⟨hs', ⟨by linarith only [ht'.2], by linarith only [ht'.1, C.r_pos]⟩⟩
      have hp' : L.project (frame w (s, t)) = base q := by
        simpa only [frame, sideSign, Bool.false_eq_true, ite_false, one_mul] using hpp
      have hm' : L.project (frame w (s', -t')) = base q := by
        simpa only [frame, sideSign, ite_true, neg_one_mul] using hmp
      have heq := C.projection_injective hplus hminus (hp'.trans hm'.symm)
      have hh := congrArg Prod.snd heq
      change t = -t' at hh
      linarith only [hh, ht.1, ht'.1]
    · exact hpoff (hmp ▸ projected_axis_mem_slit C s' hs')
  · rcases hm with ⟨hmoff, _, _, _, _, _⟩ | ⟨hmb, _, _, _⟩
    · exact hmoff (hpp ▸ projected_axis_mem_slit C s hs)
    · have h : (false : Bool) = true := hpb.symm.trans hmb
      cases h

/-- Hausdorffness is derived from the actual generated bank topology. -/
theorem cutT2Space (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w) :
    T2Space (Point L w) := by
  constructor
  intro p q hpq
  by_cases hb : base p = base q
  · have hi : base p ∈ interior L w := by
      by_contra hn
      have hp := bank_false_off_interior p hn
      have hq := bank_false_off_interior q (hb ▸ hn)
      exact hpq (point_ext hb (hp.trans hq.symm))
    obtain ⟨t, ht, ht1, htp⟩ := hi
    obtain ⟨C, htC⟩ := exists_collar_at L w hw t ⟨ht, ht1⟩
    have hbank : bank p ≠ bank q := fun h => hpq (point_ext hb h)
    have hmemp : p ∈ bankNeighborhood L w C.a C.b C.r (bank p) :=
      Or.inr ⟨rfl, t, htC, htp⟩
    have hmemq : q ∈ bankNeighborhood L w C.a C.b C.r (bank q) :=
      Or.inr ⟨rfl, t, htC, htp.trans hb⟩
    have hopen (k : Bool) : IsOpen (bankNeighborhood L w C.a C.b C.r k) :=
      bankNeighborhood_open L w C.a C.b C.r k C.a_pos C.a_lt_b C.b_lt_one C.r_pos
    cases hp : bank p <;> cases hq : bank q
    · exact False.elim (hbank (hp.trans hq.symm))
    · exact ⟨_, _, hopen false, hopen true, hp ▸ hmemp, hq ▸ hmemq,
        bankNeighborhoods_disjoint C⟩
    · exact ⟨_, _, hopen true, hopen false, hp ▸ hmemp, hq ▸ hmemq,
        (bankNeighborhoods_disjoint C).symm⟩
    · exact False.elim (hbank (hp.trans hq.symm))
  · obtain ⟨U, V, hU, hV, hp, hq, hdis⟩ := t2_separation hb
    refine ⟨base ⁻¹' U, base ⁻¹' V, hU.preimage (continuous_base L w),
      hV.preimage (continuous_base L w), hp, hq, ?_⟩
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    exact Set.disjoint_left.mp hdis hzU hzV

theorem boundaryArc_closedEmbedding (L : Lattice) (w : Plane)
    (hw : L.EmbeddedSlit w) (k : Bool) : IsClosedEmbedding (boundaryArc L w k) := by
  let : T2Space (Point L w) := cutT2Space L w hw
  exact (continuous_boundaryArc L w hw k).isClosedEmbedding (boundaryArc_injective L w hw k)

end MNEC.CutTorusBoundary
