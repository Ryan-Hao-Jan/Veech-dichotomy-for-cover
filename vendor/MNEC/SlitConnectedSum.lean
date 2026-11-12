module

public import MNEC.CutTorus
public import Mathlib.Logic.Relation
public import Mathlib.Topology.Constructions

@[expose] public section

/-!
# The cut-and-glue quotient for two arbitrary lattice tori

The two cut tori are independently defined from their physical lattices.
Only opposite banks at the same slit parameter, and matching endpoints,
are identified. A quotient invariant proves that points off the slits are
never accidentally identified, either within one torus or between them.

This constructs a topological quotient and proves its gluing laws. Flat
charts across the seam, endpoint cone charts, compactness, genus, area and
directional flows remain separate obligations.
-/

noncomputable section

namespace MNEC.SlitConnectedSum

open LatticeTorus CutTorus Set
open scoped Classical

abbrev Raw (L₁ L₂ : Lattice) (w : Plane) := Point L₁ w ⊕ Point L₂ w

inductive SeamRelation (L₁ L₂ : Lattice) (w : Plane) : Raw L₁ L₂ w → Raw L₁ L₂ w → Prop
  | upper_lower (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
      SeamRelation L₁ L₂ w
        (Sum.inl (upper L₁ w (L₁.project (t • w))))
        (Sum.inr (lower L₂ w (L₂.project (t • w)) ⟨t, ht, ht', rfl⟩))
  | lower_upper (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
      SeamRelation L₁ L₂ w
        (Sum.inl (lower L₁ w (L₁.project (t • w)) ⟨t, ht, ht', rfl⟩))
        (Sum.inr (upper L₂ w (L₂.project (t • w))))
  | initial : SeamRelation L₁ L₂ w
      (Sum.inl (upper L₁ w (L₁.project 0)))
      (Sum.inr (upper L₂ w (L₂.project 0)))
  | terminal : SeamRelation L₁ L₂ w
      (Sum.inl (upper L₁ w (L₁.project w)))
      (Sum.inr (upper L₂ w (L₂.project w)))

def gluingSetoid (L₁ L₂ : Lattice) (w : Plane) : Setoid (Raw L₁ L₂ w) :=
  Relation.EqvGen.setoid (SeamRelation L₁ L₂ w)

abbrev Surface (L₁ L₂ : Lattice) (w : Plane) := Quotient (gluingSetoid L₁ L₂ w)

def glue (L₁ L₂ : Lattice) (w : Plane) : Raw L₁ L₂ w → Surface L₁ L₂ w :=
  Quotient.mk (gluingSetoid L₁ L₂ w)

def left (L₁ L₂ : Lattice) (w : Plane) (p : Point L₁ w) : Surface L₁ L₂ w :=
  glue L₁ L₂ w (Sum.inl p)

def right (L₁ L₂ : Lattice) (w : Plane) (p : Point L₂ w) : Surface L₁ L₂ w :=
  glue L₁ L₂ w (Sum.inr p)

theorem continuous_glue (L₁ L₂ : Lattice) (w : Plane) : Continuous (glue L₁ L₂ w) :=
  continuous_quotient_mk'

theorem continuous_left (L₁ L₂ : Lattice) (w : Plane) : Continuous (left L₁ L₂ w) :=
  (continuous_glue L₁ L₂ w).comp continuous_inl

theorem continuous_right (L₁ L₂ : Lattice) (w : Plane) : Continuous (right L₁ L₂ w) :=
  (continuous_glue L₁ L₂ w).comp continuous_inr

def offLabel (L₁ L₂ : Lattice) (w : Plane) : Raw L₁ L₂ w → Option (Torus ⊕ Torus)
  | Sum.inl p => if base p ∈ L₁.slitSet w then none else some (Sum.inl (base p))
  | Sum.inr p => if base p ∈ L₂.slitSet w then none else some (Sum.inr (base p))

private theorem parameter_mem (L : Lattice) (w : Plane) (t : ℝ)
    (h₀ : 0 ≤ t) (h₁ : t ≤ 1) : L.project (t • w) ∈ L.slitSet w :=
  ⟨⟨t, h₀, h₁⟩, rfl⟩

theorem offLabel_seam {L₁ L₂ : Lattice} {w : Plane} {p q : Raw L₁ L₂ w}
    (hpq : SeamRelation L₁ L₂ w p q) : offLabel L₁ L₂ w p = offLabel L₁ L₂ w q := by
  cases hpq with
  | upper_lower t ht ht' =>
      change (if L₁.project (t • w) ∈ L₁.slitSet w then none else some (Sum.inl (L₁.project (t • w)))) =
        (if L₂.project (t • w) ∈ L₂.slitSet w then none else some (Sum.inr (L₂.project (t • w))))
      rw [ite_eq_left (parameter_mem L₁ w t ht.le ht'.le), ite_eq_left (parameter_mem L₂ w t ht.le ht'.le)]
  | lower_upper t ht ht' =>
      change (if L₁.project (t • w) ∈ L₁.slitSet w then none else some (Sum.inl (L₁.project (t • w)))) =
        (if L₂.project (t • w) ∈ L₂.slitSet w then none else some (Sum.inr (L₂.project (t • w))))
      rw [ite_eq_left (parameter_mem L₁ w t ht.le ht'.le), ite_eq_left (parameter_mem L₂ w t ht.le ht'.le)]
  | initial =>
      have h₁ := parameter_mem L₁ w 0 (by norm_num) (by norm_num)
      have h₂ := parameter_mem L₂ w 0 (by norm_num) (by norm_num)
      simp only [zero_smul] at h₁ h₂
      change (if L₁.project 0 ∈ L₁.slitSet w then none else some (Sum.inl (L₁.project 0))) =
        (if L₂.project 0 ∈ L₂.slitSet w then none else some (Sum.inr (L₂.project 0)))
      rw [ite_eq_left h₁, ite_eq_left h₂]
  | terminal =>
      have h₁ := parameter_mem L₁ w 1 (by norm_num) (by norm_num)
      have h₂ := parameter_mem L₂ w 1 (by norm_num) (by norm_num)
      simp only [one_smul] at h₁ h₂
      change (if L₁.project w ∈ L₁.slitSet w then none else some (Sum.inl (L₁.project w))) =
        (if L₂.project w ∈ L₂.slitSet w then none else some (Sum.inr (L₂.project w)))
      rw [ite_eq_left h₁, ite_eq_left h₂]

theorem offLabel_related {L₁ L₂ : Lattice} {w : Plane} {p q : Raw L₁ L₂ w}
    (hpq : Relation.EqvGen (SeamRelation L₁ L₂ w) p q) :
    offLabel L₁ L₂ w p = offLabel L₁ L₂ w q := by
  induction hpq with
  | rel _ _ h => exact offLabel_seam h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def offTrace (L₁ L₂ : Lattice) (w : Plane) : Surface L₁ L₂ w → Option (Torus ⊕ Torus) :=
  Quotient.lift (offLabel L₁ L₂ w) (fun _ _ h => offLabel_related h)

abbrev OffSlit (L : Lattice) (w : Plane) := ↥(L.slitSet w)ᶜ

def leftOff (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₁ w) : Surface L₁ L₂ w :=
  left L₁ L₂ w (upper L₁ w p)

def rightOff (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₂ w) : Surface L₁ L₂ w :=
  right L₁ L₂ w (upper L₂ w p)

@[simp] theorem offTrace_leftOff (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₁ w) :
    offTrace L₁ L₂ w (leftOff L₁ L₂ w p) = some (Sum.inl p.val) := by
  change (if p.val ∈ L₁.slitSet w then none else some (Sum.inl p.val)) = some (Sum.inl p.val)
  exact ite_eq_right p.property

@[simp] theorem offTrace_rightOff (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₂ w) :
    offTrace L₁ L₂ w (rightOff L₁ L₂ w p) = some (Sum.inr p.val) := by
  change (if p.val ∈ L₂.slitSet w then none else some (Sum.inr p.val)) = some (Sum.inr p.val)
  exact ite_eq_right p.property

theorem leftOff_injective (L₁ L₂ : Lattice) (w : Plane) : Function.Injective (leftOff L₁ L₂ w) := by
  intro p q h
  have ht := congrArg (offTrace L₁ L₂ w) h
  simp only [offTrace_leftOff, Option.some.injEq, Sum.inl.injEq] at ht
  exact Subtype.ext ht

theorem rightOff_injective (L₁ L₂ : Lattice) (w : Plane) : Function.Injective (rightOff L₁ L₂ w) := by
  intro p q h
  have ht := congrArg (offTrace L₁ L₂ w) h
  simp only [offTrace_rightOff, Option.some.injEq, Sum.inr.injEq] at ht
  exact Subtype.ext ht

theorem off_images_disjoint (L₁ L₂ : Lattice) (w : Plane) :
    Disjoint (range (leftOff L₁ L₂ w)) (range (rightOff L₁ L₂ w)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨x, rfl⟩ ⟨y, hy⟩
  have ht := congrArg (offTrace L₁ L₂ w) hy
  simp only [offTrace_leftOff, offTrace_rightOff, Option.some.injEq] at ht
  cases ht

theorem upper_lower_glued (L₁ L₂ : Lattice) (w : Plane) (t : ℝ)
    (ht : 0 < t) (ht' : t < 1) :
    left L₁ L₂ w (upper L₁ w (L₁.project (t • w))) =
      right L₁ L₂ w (lower L₂ w (L₂.project (t • w)) ⟨t, ht, ht', rfl⟩) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SeamRelation.upper_lower t ht ht'))

theorem lower_upper_glued (L₁ L₂ : Lattice) (w : Plane) (t : ℝ)
    (ht : 0 < t) (ht' : t < 1) :
    left L₁ L₂ w (lower L₁ w (L₁.project (t • w)) ⟨t, ht, ht', rfl⟩) =
      right L₁ L₂ w (upper L₂ w (L₂.project (t • w))) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (SeamRelation.lower_upper t ht ht'))

theorem initial_glued (L₁ L₂ : Lattice) (w : Plane) :
    left L₁ L₂ w (upper L₁ w (L₁.project 0)) =
      right L₁ L₂ w (upper L₂ w (L₂.project 0)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ SeamRelation.initial)

theorem terminal_glued (L₁ L₂ : Lattice) (w : Plane) :
    left L₁ L₂ w (upper L₁ w (L₁.project w)) =
      right L₁ L₂ w (upper L₂ w (L₂.project w)) :=
  Quotient.sound (Relation.EqvGen.rel _ _ SeamRelation.terminal)

end MNEC.SlitConnectedSum

