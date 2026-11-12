module

public import MNEC.SlitConnectedSum
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

/-!
# Descent of proved compatible cut maps to the actual slit surface

Two actual cut homeomorphisms which preserve the physical upper and lower
slit banks induce a homeomorphism of the independently defined cross-glue
quotients. This is functoriality of the exact seam relation. It does not
assume a same-surface twist, and does not assert affine or area compatibility.
Computed lattice rebasing will supply the compatible cut maps separately.
-/

noncomputable section

namespace MNEC.SlitSurfaceCongruence

open LatticeTorus CutTorus SlitConnectedSum

variable {L M : Lattice} {w : Plane}

def BankCompatible (e : Point M w ≃ₜ Point L w) : Prop :=
  (∀ x : Plane, e (upper M w (M.project x)) = upper L w (L.project x)) ∧
    ∀ (t : ℝ) (ht : 0 < t) (ht' : t < 1),
      e (lower M w (M.project (t • w)) ⟨t, ht, ht', rfl⟩) =
        lower L w (L.project (t • w)) ⟨t, ht, ht', rfl⟩

theorem BankCompatible.symm (e : Point M w ≃ₜ Point L w) (h : BankCompatible e) :
    BankCompatible e.symm := by
  constructor
  · intro x
    apply e.injective
    rw [e.apply_symm_apply, h.1]
  · intro t ht ht'
    apply e.injective
    rw [e.apply_symm_apply, h.2 t ht ht']

section TwoPieces

variable {L₁ L₂ M₁ M₂ : Lattice}

def rawHomeomorph (e₁ : Point M₁ w ≃ₜ Point L₁ w) (e₂ : Point M₂ w ≃ₜ Point L₂ w) :
    Raw M₁ M₂ w ≃ₜ Raw L₁ L₂ w := Homeomorph.sumCongr e₁ e₂

theorem seam_preserved (e₁ : Point M₁ w ≃ₜ Point L₁ w) (e₂ : Point M₂ w ≃ₜ Point L₂ w)
    (h₁ : BankCompatible e₁) (h₂ : BankCompatible e₂)
    {p q : Raw M₁ M₂ w} (hpq : SeamRelation M₁ M₂ w p q) :
    SeamRelation L₁ L₂ w (rawHomeomorph e₁ e₂ p) (rawHomeomorph e₁ e₂ q) := by
  cases hpq with
  | upper_lower t ht ht' =>
    change SeamRelation L₁ L₂ w (Sum.inl (e₁ _)) (Sum.inr (e₂ _))
    rw [h₁.1, h₂.2 t ht ht']
    exact SeamRelation.upper_lower t ht ht'
  | lower_upper t ht ht' =>
    change SeamRelation L₁ L₂ w (Sum.inl (e₁ _)) (Sum.inr (e₂ _))
    rw [h₁.2 t ht ht', h₂.1]
    exact SeamRelation.lower_upper t ht ht'
  | initial =>
    change SeamRelation L₁ L₂ w (Sum.inl (e₁ _)) (Sum.inr (e₂ _))
    rw [h₁.1, h₂.1]
    exact SeamRelation.initial
  | terminal =>
    change SeamRelation L₁ L₂ w (Sum.inl (e₁ _)) (Sum.inr (e₂ _))
    rw [h₁.1, h₂.1]
    exact SeamRelation.terminal

theorem related_preserved (e₁ : Point M₁ w ≃ₜ Point L₁ w) (e₂ : Point M₂ w ≃ₜ Point L₂ w)
    (h₁ : BankCompatible e₁) (h₂ : BankCompatible e₂)
    {p q : Raw M₁ M₂ w} (hpq : Relation.EqvGen (SeamRelation M₁ M₂ w) p q) :
    Relation.EqvGen (SeamRelation L₁ L₂ w)
      (rawHomeomorph e₁ e₂ p) (rawHomeomorph e₁ e₂ q) := by
  induction hpq with
  | rel _ _ h => exact Relation.EqvGen.rel _ _ (seam_preserved e₁ e₂ h₁ h₂ h)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem related_iff (e₁ : Point M₁ w ≃ₜ Point L₁ w) (e₂ : Point M₂ w ≃ₜ Point L₂ w)
    (h₁ : BankCompatible e₁) (h₂ : BankCompatible e₂) (p q : Raw M₁ M₂ w) :
    Relation.EqvGen (SeamRelation M₁ M₂ w) p q ↔
      Relation.EqvGen (SeamRelation L₁ L₂ w)
        (rawHomeomorph e₁ e₂ p) (rawHomeomorph e₁ e₂ q) := by
  constructor
  · exact related_preserved e₁ e₂ h₁ h₂
  · intro h
    have hback := related_preserved e₁.symm e₂.symm
      (h₁.symm e₁) (h₂.symm e₂) h
    have hp : rawHomeomorph e₁.symm e₂.symm (rawHomeomorph e₁ e₂ p) = p :=
      (rawHomeomorph e₁ e₂).symm_apply_apply p
    have hq : rawHomeomorph e₁.symm e₂.symm (rawHomeomorph e₁ e₂ q) = q :=
      (rawHomeomorph e₁ e₂).symm_apply_apply q
    rwa [hp, hq] at hback

def surfaceHomeomorph (e₁ : Point M₁ w ≃ₜ Point L₁ w) (e₂ : Point M₂ w ≃ₜ Point L₂ w)
    (h₁ : BankCompatible e₁) (h₂ : BankCompatible e₂) :
    Surface M₁ M₂ w ≃ₜ Surface L₁ L₂ w :=
  Homeomorph.Quotient.congr (rawHomeomorph e₁ e₂) (related_iff e₁ e₂ h₁ h₂)

theorem surfaceHomeomorph_glue (e₁ : Point M₁ w ≃ₜ Point L₁ w)
    (e₂ : Point M₂ w ≃ₜ Point L₂ w) (h₁ : BankCompatible e₁) (h₂ : BankCompatible e₂)
    (p : Raw M₁ M₂ w) :
    surfaceHomeomorph e₁ e₂ h₁ h₂ (glue M₁ M₂ w p) =
      glue L₁ L₂ w (rawHomeomorph e₁ e₂ p) := rfl

theorem surfaceHomeomorph_left (e₁ : Point M₁ w ≃ₜ Point L₁ w)
    (e₂ : Point M₂ w ≃ₜ Point L₂ w) (h₁ : BankCompatible e₁) (h₂ : BankCompatible e₂)
    (p : Point M₁ w) :
    surfaceHomeomorph e₁ e₂ h₁ h₂ (left M₁ M₂ w p) = left L₁ L₂ w (e₁ p) := rfl

theorem surfaceHomeomorph_right (e₁ : Point M₁ w ≃ₜ Point L₁ w)
    (e₂ : Point M₂ w ≃ₜ Point L₂ w) (h₁ : BankCompatible e₁) (h₂ : BankCompatible e₂)
    (p : Point M₂ w) :
    surfaceHomeomorph e₁ e₂ h₁ h₂ (right M₁ M₂ w p) = right L₁ L₂ w (e₂ p) := rfl

end TwoPieces

end MNEC.SlitSurfaceCongruence

