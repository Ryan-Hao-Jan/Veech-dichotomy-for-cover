module

public import MNEC.SlitCollars

@[expose] public section

/-!
# Continuous lifts of the two half-collars to the actual cut torus

The zero-normal boundary is sent to its specified bank; a point strictly
above that boundary is sent to the corresponding physical side of the slit.
Continuity is proved directly on the generators of the cut topology.
No continuity assumption is included in the collar or lift definitions.
-/

noncomputable section

namespace MNEC.CutBankLifts

open LatticeTorus CutTorus OffSlitEmbeddings SlitCollars Set Topology Filter
open scoped Classical

def interiorBank (L : Lattice) (w : Plane) (k : Bool) (s : ℝ)
    (hs : 0 < s ∧ s < 1) : Point L w :=
  ⟨(L.project (s • w), k), Or.inr ⟨s, hs.1, hs.2, rfl⟩⟩

@[simp] theorem base_interiorBank (L : Lattice) (w : Plane) (k : Bool) (s : ℝ)
    (hs : 0 < s ∧ s < 1) : base (interiorBank L w k s hs) = L.project (s • w) := rfl

@[simp] theorem bank_interiorBank (L : Lattice) (w : Plane) (k : Bool) (s : ℝ)
    (hs : 0 < s ∧ s < 1) : bank (interiorBank L w k s hs) = k := rfl

theorem interiorBank_false (L : Lattice) (w : Plane) (s : ℝ) (hs : 0 < s ∧ s < 1) :
    interiorBank L w false s hs = upper L w (L.project (s • w)) := rfl

theorem interiorBank_true (L : Lattice) (w : Plane) (s : ℝ) (hs : 0 < s ∧ s < 1) :
    interiorBank L w true s hs =
      lower L w (L.project (s • w)) ⟨s, hs.1, hs.2, rfl⟩ := rfl

theorem mem_bankNeighborhood_interiorBank (L : Lattice) (w : Plane)
    (hw : L.EmbeddedSlit w) (k l : Bool) (a b r s : ℝ)
    (ha : 0 < a) (hb : b < 1) (hs : 0 < s ∧ s < 1) :
    interiorBank L w k s hs ∈ bankNeighborhood L w a b r l ↔
      s ∈ Ioo a b ∧ k = l := by
  constructor
  · intro hmem
    rcases hmem with ⟨hnot, _⟩ | ⟨hbank, s', hs', heq⟩
    · exact False.elim (hnot ⟨⟨s, hs.1.le, hs.2.le⟩, rfl⟩)
    · have hsi : s' ∈ Icc (0 : ℝ) 1 :=
        ⟨(ha.trans hs'.1).le, (hs'.2.trans hb).le⟩
      have hst : s' = s := congrArg Subtype.val
        (hw (show L.arc w ⟨s', hsi⟩ = L.arc w ⟨s, hs.1.le, hs.2.le⟩ from heq))
      exact ⟨hst ▸ hs', hbank⟩
  · rintro ⟨ht, hkl⟩
    exact Or.inr ⟨hkl, s, ht, rfl⟩

abbrev HalfDomain {L : Lattice} {w : Plane} (C : Collar L w) :=
  {q : Plane // q ∈ domain C ∧ 0 ≤ q.2}

def halfPosition {L : Lattice} {w : Plane} {C : Collar L w}
    (k : Bool) (q : HalfDomain C) : Plane := (q.val.1, sideSign k * q.val.2)

theorem halfPosition_mem {L : Lattice} {w : Plane} (C : Collar L w)
    (k : Bool) (q : HalfDomain C) : halfPosition k q ∈ domain C := by
  have hq := q.property.1
  change q.val.1 ∈ Ioo C.a C.b ∧ q.val.2 ∈ Ioo (-C.r) C.r at hq
  change q.val.1 ∈ Ioo C.a C.b ∧ sideSign k * q.val.2 ∈ Ioo (-C.r) C.r
  cases k with
  | false => simpa [sideSign] using hq
  | true =>
    simp only [sideSign, ite_true, neg_one_mul]
    exact ⟨hq.1, ⟨by linarith only [hq.2.2], by linarith only [hq.2.1]⟩⟩

def halfBase {L : Lattice} {w : Plane} {C : Collar L w}
    (k : Bool) (q : HalfDomain C) : Torus := L.project (frame w (halfPosition k q))

theorem halfLongitudinal {L : Lattice} {w : Plane} {C : Collar L w}
    (q : HalfDomain C) : 0 < q.val.1 ∧ q.val.1 < 1 :=
  ⟨(domain_longitudinal C q.property.1).1, (domain_longitudinal C q.property.1).2⟩

def halfLift {L : Lattice} {w : Plane} (C : Collar L w)
    (k : Bool) (q : HalfDomain C) : Point L w :=
  if q.val.2 = 0 then
    interiorBank L w k q.val.1 (halfLongitudinal q)
  else upper L w (halfBase k q)

theorem halfLift_zero {L : Lattice} {w : Plane} (C : Collar L w)
    (k : Bool) (q : HalfDomain C) (hq : q.val.2 = 0) :
    halfLift C k q = interiorBank L w k q.val.1 (halfLongitudinal q) :=
  ite_eq_left hq

theorem halfLift_nonzero {L : Lattice} {w : Plane} (C : Collar L w)
    (k : Bool) (q : HalfDomain C) (hq : q.val.2 ≠ 0) :
    halfLift C k q = upper L w (halfBase k q) := ite_eq_right hq

theorem continuous_halfBase {L : Lattice} {w : Plane} (C : Collar L w) (k : Bool) :
    Continuous (halfBase (C := C) k) :=
  L.continuous_project.comp ((continuous_frame w).comp
    ((continuous_subtype_val.fst).prodMk (continuous_const.mul continuous_subtype_val.snd)))

theorem base_halfLift {L : Lattice} {w : Plane} (C : Collar L w)
    (k : Bool) (q : HalfDomain C) : base (halfLift C k q) = halfBase k q := by
  by_cases hq : q.val.2 = 0
  · rw [halfLift_zero C k q hq, base_interiorBank]
    simp [halfBase, halfPosition, frame, hq]
  · rw [halfLift_nonzero C k q hq]
    rfl

theorem halfBase_off_slit {L : Lattice} {w : Plane} (C : Collar L w)
    (k : Bool) (q : HalfDomain C) (hq : q.val.2 ≠ 0) : halfBase k q ∉ L.slitSet w := by
  intro hslit
  have hh := (C.slit_iff _ (halfPosition_mem C k q)).mp hslit
  change sideSign k * q.val.2 = 0 at hh
  cases k with
  | false => exact hq (by simpa [sideSign] using hh)
  | true =>
    simp only [sideSign, ite_true, neg_one_mul] at hh
    exact hq (neg_eq_zero.mp hh)

theorem bank_preimage_open {L : Lattice} {w : Plane} (hw : L.EmbeddedSlit w)
    (C : Collar L w) (k l : Bool) (a b r : ℝ)
    (ha : 0 < a) (hb : b < 1) (hr : 0 < r) :
    IsOpen (halfLift C k ⁻¹' bankNeighborhood L w a b r l) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  by_cases hzero : q.val.2 = 0
  · rw [Set.mem_preimage, halfLift_zero C k q hzero,
      mem_bankNeighborhood_interiorBank L w hw k l a b r q.val.1 ha hb] at hq
    have hk : k = l := hq.2
    let V : Set (HalfDomain C) := {p | p.val.1 ∈ Ioo a b ∧ p.val.2 < r}
    have hV : IsOpen V := (isOpen_Ioo.preimage continuous_subtype_val.fst).inter
      (isOpen_Iio.preimage continuous_subtype_val.snd)
    have hqV : q ∈ V := ⟨hq.1, by rw [hzero]; exact hr⟩
    apply Filter.mem_of_superset (hV.mem_nhds hqV)
    intro p hp
    by_cases hp0 : p.val.2 = 0
    · rw [Set.mem_preimage, halfLift_zero C k p hp0,
        mem_bankNeighborhood_interiorBank L w hw k l a b r p.val.1 ha hb]
      exact ⟨hp.1, hk⟩
    · rw [Set.mem_preimage, halfLift_nonzero C k p hp0]
      refine Or.inl ⟨halfBase_off_slit C k p hp0, p.val.1, hp.1, p.val.2,
        ⟨lt_of_le_of_ne p.property.2 (Ne.symm hp0), hp.2⟩, ?_⟩
      rw [← hk]
      rfl
  · have hqp : 0 < q.val.2 := lt_of_le_of_ne q.property.2 (Ne.symm hzero)
    have hstrip : halfBase k q ∈ signedStrip L w a b r l := by
      rw [Set.mem_preimage, halfLift_nonzero C k q hzero] at hq
      rcases hq with ⟨_, hs⟩ | ⟨_, s, hs, heq⟩
      · exact hs
      · exact False.elim (halfBase_off_slit C k q hzero
          ⟨⟨s, (ha.trans hs.1).le, (hs.2.trans hb).le⟩, heq⟩)
    let V : Set (HalfDomain C) :=
      {p | 0 < p.val.2 ∧ halfBase k p ∈ signedStrip L w a b r l}
    have hV : IsOpen V := (isOpen_Ioi.preimage continuous_subtype_val.snd).inter
      ((signedStrip_open L w (embeddedSlit_ne_zero L w hw) a b r l).preimage
        (continuous_halfBase C k))
    apply Filter.mem_of_superset (hV.mem_nhds ⟨hqp, hstrip⟩)
    intro p hp
    have hp0 : p.val.2 ≠ 0 := ne_of_gt hp.1
    rw [Set.mem_preimage, halfLift_nonzero C k p hp0]
    exact Or.inl ⟨halfBase_off_slit C k p hp0, hp.2⟩

theorem continuous_halfLift {L : Lattice} {w : Plane} (hw : L.EmbeddedSlit w)
    (C : Collar L w) (k : Bool) : Continuous (halfLift C k) := by
  apply continuous_generateFrom_iff.mpr
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩ | ⟨a, b, r, l, ha, _hab, hb, hr, rfl⟩
  · have heq : halfLift C k ⁻¹' (base ⁻¹' V) = halfBase k ⁻¹' V := by
      ext q
      simp only [Set.mem_preimage, base_halfLift]
    rw [heq]
    exact hV.preimage (continuous_halfBase C k)
  · exact bank_preimage_open hw C k l a b r ha hb hr

theorem halfBase_injective {L : Lattice} {w : Plane} (C : Collar L w) (k : Bool) :
    Function.Injective (halfBase (C := C) k) := by
  intro p q heq
  have hpq := C.projection_injective (halfPosition_mem C k p) (halfPosition_mem C k q) heq
  have h₁ := congrArg Prod.fst hpq
  have h₂ := congrArg Prod.snd hpq
  apply Subtype.ext
  apply Prod.ext
  · exact h₁
  · cases k <;> simpa [halfPosition, sideSign] using h₂

theorem halfLift_injective {L : Lattice} {w : Plane} (C : Collar L w) (k : Bool) :
    Function.Injective (halfLift C k) := by
  intro p q heq
  apply halfBase_injective C k
  simpa only [base_halfLift] using congrArg base heq

end MNEC.CutBankLifts
