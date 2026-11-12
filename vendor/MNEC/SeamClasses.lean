module

public import MNEC.CutBankLifts

@[expose] public section

/-!
# Exact equivalence classes of the physical seam gluing

For embedded slits the elementary seam relation is a bipartite matching.
Its generated equivalence relation consequently adds only reflexivity and
symmetry: no longer chain identifies further points. This is proved from
the actual seam constructors and the two embedded arc maps.
-/

noncomputable section

namespace MNEC.SeamClasses

open LatticeTorus CutTorus SlitConnectedSum CutBankLifts Set
open scoped Classical

section Matching

variable {A : Type*} (r : A → A → Prop)
    (hfun : ∀ ⦃a b c⦄, r a b → r a c → b = c)
    (hrev : ∀ ⦃a b c⦄, r a c → r b c → a = b)
    (hno : ∀ ⦃a b c⦄, r a b → r b c → False)

include hfun hrev hno

theorem matching_trans {a b c : A}
    (hab : a = b ∨ r a b ∨ r b a) (hbc : b = c ∨ r b c ∨ r c b) :
    a = c ∨ r a c ∨ r c a := by
  rcases hab with rfl | hab | hba
  · exact hbc
  · rcases hbc with rfl | hbc | hcb
    · exact Or.inr (Or.inl hab)
    · exact False.elim (hno hab hbc)
    · exact Or.inl (hrev hab hcb)
  · rcases hbc with rfl | hbc | hcb
    · exact Or.inr (Or.inr hba)
    · exact Or.inl (hfun hba hbc)
    · exact False.elim (hno hcb hba)

/-- Equivalence closure of a bipartite partial matching has no nontrivial
chains beyond a single edge. -/
theorem matching_eqvGen_iff (a b : A) :
    Relation.EqvGen r a b ↔ a = b ∨ r a b ∨ r b a := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact Or.inr (Or.inl h)
    | refl => exact Or.inl rfl
    | symm _ _ _ ih =>
        rcases ih with h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
    | trans _ _ _ _ _ ih₁ ih₂ => exact matching_trans r hfun hrev hno ih₁ ih₂
  · rintro (h | h | h)
    · subst b
      exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)

end Matching

def oppositeBank (t : Parameter) (k : Bool) : Bool :=
  if 0 < (t : ℝ) ∧ (t : ℝ) < 1 then !k else false

theorem seam_bipartite {L₁ L₂ : Lattice} {w : Plane} {p q : Raw L₁ L₂ w}
    (h : SeamRelation L₁ L₂ w p q) :
    ∃ x : Point L₁ w, ∃ y : Point L₂ w, p = Sum.inl x ∧ q = Sum.inr y := by
  cases h <;> exact ⟨_, _, rfl, rfl⟩

theorem seam_parameter_data {L₁ L₂ : Lattice} {w : Plane}
    {x : Point L₁ w} {y : Point L₂ w}
    (h : SeamRelation L₁ L₂ w (Sum.inl x) (Sum.inr y)) :
    ∃ t : Parameter,
      base x = L₁.arc w t ∧ base y = L₂.arc w t ∧
      bank x = oppositeBank t (bank y) ∧ bank y = oppositeBank t (bank x) := by
  cases h with
  | upper_lower t ht ht' =>
      refine ⟨⟨t, ht.le, ht'.le⟩, rfl, rfl, ?_, ?_⟩ <;>
        simp [oppositeBank, bank, lower, upper, ht, ht']
  | lower_upper t ht ht' =>
      refine ⟨⟨t, ht.le, ht'.le⟩, rfl, rfl, ?_, ?_⟩ <;>
        simp [oppositeBank, bank, lower, upper, ht, ht']
  | initial =>
      refine ⟨⟨0, by constructor <;> norm_num⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp [Lattice.arc, oppositeBank]
  | terminal =>
      refine ⟨⟨1, by constructor <;> norm_num⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp [Lattice.arc, oppositeBank]

theorem seam_functional_left {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) {x : Point L₁ w} {y z : Point L₂ w}
    (hxy : SeamRelation L₁ L₂ w (Sum.inl x) (Sum.inr y))
    (hxz : SeamRelation L₁ L₂ w (Sum.inl x) (Sum.inr z)) : y = z := by
  obtain ⟨s, hxs, hys, _, hby⟩ := seam_parameter_data hxy
  obtain ⟨t, hxt, hzt, _, hbz⟩ := seam_parameter_data hxz
  have hst : s = t := hw₁ (hxs.symm.trans hxt)
  subst t
  exact point_ext (hys.trans hzt.symm) (hby.trans hbz.symm)

theorem seam_source_on_slit {L₁ L₂ : Lattice} {w : Plane}
    {x : Point L₁ w} {y : Point L₂ w}
    (h : SeamRelation L₁ L₂ w (Sum.inl x) (Sum.inr y)) : base x ∈ L₁.slitSet w := by
  obtain ⟨t, hx, _⟩ := seam_parameter_data h
  rw [hx]
  exact ⟨t, rfl⟩

theorem seam_target_on_slit {L₁ L₂ : Lattice} {w : Plane}
    {x : Point L₁ w} {y : Point L₂ w}
    (h : SeamRelation L₁ L₂ w (Sum.inl x) (Sum.inr y)) : base y ∈ L₂.slitSet w := by
  obtain ⟨t, _, hy, _⟩ := seam_parameter_data h
  rw [hy]
  exact ⟨t, rfl⟩

theorem seam_functional_right {L₁ L₂ : Lattice} {w : Plane}
    (hw₂ : L₂.EmbeddedSlit w) {x z : Point L₁ w} {y : Point L₂ w}
    (hxy : SeamRelation L₁ L₂ w (Sum.inl x) (Sum.inr y))
    (hzy : SeamRelation L₁ L₂ w (Sum.inl z) (Sum.inr y)) : x = z := by
  obtain ⟨s, hxs, hys, hbx, _⟩ := seam_parameter_data hxy
  obtain ⟨t, hzt, hyt, hbz, _⟩ := seam_parameter_data hzy
  have hst : s = t := hw₂ (hys.symm.trans hyt)
  subst t
  exact point_ext (hxs.trans hzt.symm) (hbx.trans hbz.symm)

theorem seam_functional {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) {p q s : Raw L₁ L₂ w}
    (hpq : SeamRelation L₁ L₂ w p q) (hps : SeamRelation L₁ L₂ w p s) : q = s := by
  obtain ⟨x, y, rfl, rfl⟩ := seam_bipartite hpq
  obtain ⟨x', z, hx, rfl⟩ := seam_bipartite hps
  have hxx : x = x' := Sum.inl.inj hx
  subst x'
  exact congrArg Sum.inr (seam_functional_left hw₁ hpq hps)

theorem seam_reverse_functional {L₁ L₂ : Lattice} {w : Plane}
    (hw₂ : L₂.EmbeddedSlit w) {p q s : Raw L₁ L₂ w}
    (hps : SeamRelation L₁ L₂ w p s) (hqs : SeamRelation L₁ L₂ w q s) : p = q := by
  obtain ⟨x, y, rfl, rfl⟩ := seam_bipartite hps
  obtain ⟨z, y', rfl, hy⟩ := seam_bipartite hqs
  have hyy : y = y' := Sum.inr.inj hy
  subst y'
  exact congrArg Sum.inl (seam_functional_right hw₂ hps hqs)

theorem seam_no_two_step {L₁ L₂ : Lattice} {w : Plane} {p q s : Raw L₁ L₂ w}
    (hpq : SeamRelation L₁ L₂ w p q) (hqs : SeamRelation L₁ L₂ w q s) : False := by
  obtain ⟨x, y, rfl, rfl⟩ := seam_bipartite hpq
  cases hqs

theorem eqvGen_iff (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (p q : Raw L₁ L₂ w) :
    Relation.EqvGen (SeamRelation L₁ L₂ w) p q ↔
      p = q ∨ SeamRelation L₁ L₂ w p q ∨ SeamRelation L₁ L₂ w q p :=
  matching_eqvGen_iff (SeamRelation L₁ L₂ w)
    (fun {_ _ _} h₁ h₂ => seam_functional hw₁ h₁ h₂)
    (fun {_ _ _} h₁ h₂ => seam_reverse_functional hw₂ h₁ h₂)
    (fun {_ _ _} h₁ h₂ => seam_no_two_step h₁ h₂) p q

theorem glue_eq_iff (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (p q : Raw L₁ L₂ w) :
    glue L₁ L₂ w p = glue L₁ L₂ w q ↔
      p = q ∨ SeamRelation L₁ L₂ w p q ∨ SeamRelation L₁ L₂ w q p := by
  constructor
  · intro h
    exact (eqvGen_iff L₁ L₂ w hw₁ hw₂ p q).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((eqvGen_iff L₁ L₂ w hw₁ hw₂ p q).mpr h)

theorem left_injective (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    Function.Injective (left L₁ L₂ w) := by
  intro p q hpq
  rcases (glue_eq_iff L₁ L₂ w hw₁ hw₂ (Sum.inl p) (Sum.inl q)).mp hpq with h | h | h
  · exact Sum.inl.inj h
  · cases h
  · cases h

theorem right_injective (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    Function.Injective (right L₁ L₂ w) := by
  intro p q hpq
  rcases (glue_eq_iff L₁ L₂ w hw₁ hw₂ (Sum.inr p) (Sum.inr q)).mp hpq with h | h | h
  · exact Sum.inr.inj h
  · cases h
  · cases h

theorem left_eq_right_iff (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (p : Point L₁ w) (q : Point L₂ w) :
    left L₁ L₂ w p = right L₁ L₂ w q ↔
      SeamRelation L₁ L₂ w (Sum.inl p) (Sum.inr q) := by
  constructor
  · intro hpq
    rcases (glue_eq_iff L₁ L₂ w hw₁ hw₂ (Sum.inl p) (Sum.inr q)).mp hpq with h | h | h
    · cases h
    · exact h
    · cases h
  · intro h
    exact Quotient.sound (Relation.EqvGen.rel _ _ h)

theorem interior_seam_iff (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (k l : Bool) (s t : ℝ) (hs : 0 < s ∧ s < 1) (ht : 0 < t ∧ t < 1) :
    SeamRelation L₁ L₂ w (Sum.inl (interiorBank L₁ w k s hs))
      (Sum.inr (interiorBank L₂ w l t ht)) ↔ s = t ∧ l = !k := by
  constructor
  · intro h
    obtain ⟨u, hsu, htu, _, hb⟩ := seam_parameter_data h
    have hsu' : s = (u : ℝ) := congrArg Subtype.val
      (hw₁ (show L₁.arc w ⟨s, hs.1.le, hs.2.le⟩ = L₁.arc w u from hsu))
    have htu' : t = (u : ℝ) := congrArg Subtype.val
      (hw₂ (show L₂.arc w ⟨t, ht.1.le, ht.2.le⟩ = L₂.arc w u from htu))
    refine ⟨hsu'.trans htu'.symm, ?_⟩
    change l = oppositeBank u k at hb
    simpa [oppositeBank, ← hsu', hs.1, hs.2] using hb
  · rintro ⟨rfl, rfl⟩
    cases k
    · exact SeamRelation.upper_lower _ hs.1 hs.2
    · exact SeamRelation.lower_upper _ hs.1 hs.2

theorem left_interiorBank_eq_iff (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (k l : Bool) (s t : ℝ) (hs : 0 < s ∧ s < 1) (ht : 0 < t ∧ t < 1) :
    left L₁ L₂ w (interiorBank L₁ w k s hs) =
      left L₁ L₂ w (interiorBank L₁ w l t ht) ↔ s = t ∧ k = l := by
  constructor
  · intro h
    have heq := left_injective L₁ L₂ w hw₁ hw₂ h
    have hbase := congrArg base heq
    have hbank := congrArg bank heq
    exact ⟨congrArg Subtype.val (hw₁
      (show L₁.arc w ⟨s, hs.1.le, hs.2.le⟩ =
        L₁.arc w ⟨t, ht.1.le, ht.2.le⟩ from hbase)), hbank⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem initial_ne_terminal (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    left L₁ L₂ w (upper L₁ w (L₁.project 0)) ≠
      left L₁ L₂ w (upper L₁ w (L₁.project w)) := by
  intro h
  have hb := congrArg base (left_injective L₁ L₂ w hw₁ hw₂ h)
  have heq : L₁.arc w ⟨0, by constructor <;> norm_num⟩ =
      L₁.arc w ⟨1, by constructor <;> norm_num⟩ := by
    simpa [Lattice.arc] using hb
  have h01 := congrArg Subtype.val (hw₁ heq)
  norm_num at h01

end MNEC.SeamClasses
