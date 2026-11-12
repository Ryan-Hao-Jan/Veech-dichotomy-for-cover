module

public import MNEC.CutTorusBoundary
public import MNEC.SeamClasses
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
# Hausdorff separation of the actual slit-gluing quotient

The nontrivial identifications form a compact relation, parametrized by
the two closed slit-bank arcs and their reverses. Saturations of closed
sets are therefore closed and fibers are compact. The actual quotient map
is proper, and its product sends the closed diagonal to a closed diagonal.
Thus Hausdorffness is proved without assuming compactness of either cut
torus or of the surface.
-/

noncomputable section

namespace MNEC.SlitQuotientSeparation

open LatticeTorus CutTorus CutBankLifts CutTorusBoundary SlitConnectedSum SeamClasses
open Set Topology Function
open scoped Classical

section CompactIdentification

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

omit [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] in
theorem saturation_eq (f : X → Y) (K : Set (X × X))
    (hrel : ∀ x y, f x = f y ↔ x = y ∨ (x, y) ∈ K) (A : Set X) :
    f ⁻¹' (f '' A) = A ∪ Prod.snd '' (K ∩ Prod.fst ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    rcases (hrel a x).1 hax with rfl | hK
    · exact Or.inl ha
    · exact Or.inr ⟨(a, x), ⟨hK, ha⟩, rfl⟩
  · rintro (hx | ⟨⟨a, b⟩, ⟨hK, ha⟩, hbx⟩)
    · exact ⟨x, hx, rfl⟩
    · change b = x at hbx
      subst b
      exact ⟨a, ha, (hrel a x).2 (Or.inr hK)⟩

theorem isClosedMap_of_compact_identification (f : X → Y) (hq : IsQuotientMap f)
    (K : Set (X × X)) (hK : IsCompact K)
    (hrel : ∀ x y, f x = f y ↔ x = y ∨ (x, y) ∈ K) : IsClosedMap f := by
  intro A hA
  apply hq.isClosed_preimage.mp
  rw [saturation_eq f K hrel A]
  exact hA.union (((hK.inter_right (hA.preimage continuous_fst)).image continuous_snd).isClosed)

omit [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] in
theorem fiber_eq (f : X → Y) (K : Set (X × X))
    (hrel : ∀ x y, f x = f y ↔ x = y ∨ (x, y) ∈ K) (a : X) :
    f ⁻¹' {f a} = {a} ∪ Prod.snd '' (K ∩ Prod.fst ⁻¹' {a}) := by
  ext x
  constructor
  · intro hx
    have hax : f a = f x := hx.symm
    rcases (hrel a x).1 hax with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨(a, x), ⟨h, rfl⟩, rfl⟩
  · rintro (hx | ⟨⟨b, c⟩, ⟨hK, hb⟩, hcx⟩)
    · change x = a at hx
      subst x
      rfl
    · change b = a at hb
      change c = x at hcx
      subst b
      subst c
      exact ((hrel a x).2 (Or.inr hK)).symm

theorem isProperMap_of_compact_identification (f : X → Y) (hq : IsQuotientMap f)
    (K : Set (X × X)) (hK : IsCompact K)
    (hrel : ∀ x y, f x = f y ↔ x = y ∨ (x, y) ∈ K) : IsProperMap f := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hq.continuous, isClosedMap_of_compact_identification f hq K hK hrel, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := hq.surjective y
  rw [fiber_eq f K hrel a]
  exact isCompact_singleton.union
    ((hK.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd)

theorem t2Space_of_compact_identification (f : X → Y) (hq : IsQuotientMap f)
    (K : Set (X × X)) (hK : IsCompact K)
    (hrel : ∀ x y, f x = f y ↔ x = y ∨ (x, y) ∈ K) : T2Space Y := by
  have hp := isProperMap_of_compact_identification f hq K hK hrel
  have hdiag : Prod.map f f '' diagonal X = diagonal Y := by
    ext ⟨y, z⟩
    constructor
    · rintro ⟨⟨a, b⟩, hab, heq⟩
      change a = b at hab
      subst b
      have h₁ : f a = y := congrArg Prod.fst heq
      have h₂ : f a = z := congrArg Prod.snd heq
      exact h₁.symm.trans h₂
    · intro hyz
      change y = z at hyz
      subst z
      obtain ⟨a, rfl⟩ := hq.surjective y
      exact ⟨(a, a), rfl, rfl⟩
  apply t2_iff_isClosed_diagonal.mpr
  rw [← hdiag]
  exact (hp.prodMap hp).isClosedMap _ isClosed_diagonal

end CompactIdentification

def bankGraph (L₁ L₂ : Lattice) (w : Plane) (k : Bool) :
    Set (Raw L₁ L₂ w × Raw L₁ L₂ w) :=
  range fun t : Parameter =>
    (Sum.inl (boundaryArc L₁ w k t), Sum.inr (boundaryArc L₂ w (!k) t))

theorem bankGraph_compact (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (k : Bool) :
    IsCompact (bankGraph L₁ L₂ w k) :=
  isCompact_range ((continuous_inl.comp (continuous_boundaryArc L₁ w hw₁ k)).prodMk
    (continuous_inr.comp (continuous_boundaryArc L₂ w hw₂ (!k))))

theorem seam_boundaryArc (L₁ L₂ : Lattice) (w : Plane) (k : Bool) (t : Parameter) :
    SeamRelation L₁ L₂ w (Sum.inl (boundaryArc L₁ w k t))
      (Sum.inr (boundaryArc L₂ w (!k) t)) := by
  by_cases hzero : (t : ℝ) = 0
  · have ht : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext hzero
    subst t
    rw [boundaryArc_zero, boundaryArc_zero]
    exact SeamRelation.initial
  by_cases hone : (t : ℝ) = 1
  · have ht : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hone
    subst t
    rw [boundaryArc_one, boundaryArc_one]
    exact SeamRelation.terminal
  have ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1 :=
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm hzero), lt_of_le_of_ne t.property.2 hone⟩
  rw [boundaryArc_interior L₁ w k t ht, boundaryArc_interior L₂ w (!k) t ht]
  cases k with
  | false => exact SeamRelation.upper_lower t ht.1 ht.2
  | true => exact SeamRelation.lower_upper t ht.1 ht.2

def forwardGraph (L₁ L₂ : Lattice) (w : Plane) : Set (Raw L₁ L₂ w × Raw L₁ L₂ w) :=
  bankGraph L₁ L₂ w false ∪ bankGraph L₁ L₂ w true

theorem forwardGraph_mem_iff (L₁ L₂ : Lattice) (w : Plane) (p q : Raw L₁ L₂ w) :
    (p, q) ∈ forwardGraph L₁ L₂ w ↔ SeamRelation L₁ L₂ w p q := by
  constructor
  · rintro (⟨t, heq⟩ | ⟨t, heq⟩)
    · have hp := congrArg Prod.fst heq
      have hq := congrArg Prod.snd heq
      change Sum.inl (boundaryArc L₁ w false t) = p at hp
      change Sum.inr (boundaryArc L₂ w (!false) t) = q at hq
      rw [← hp, ← hq]
      exact seam_boundaryArc L₁ L₂ w false t
    · have hp := congrArg Prod.fst heq
      have hq := congrArg Prod.snd heq
      change Sum.inl (boundaryArc L₁ w true t) = p at hp
      change Sum.inr (boundaryArc L₂ w (!true) t) = q at hq
      rw [← hp, ← hq]
      exact seam_boundaryArc L₁ L₂ w true t
  · intro h
    cases h with
    | upper_lower t ht ht' =>
      left
      let ti : Parameter := ⟨t, ht.le, ht'.le⟩
      refine ⟨ti, ?_⟩
      dsimp only
      rw [boundaryArc_false, boundaryArc_interior L₂ w (!false) ti ⟨ht, ht'⟩]
      rfl
    | lower_upper t ht ht' =>
      right
      let ti : Parameter := ⟨t, ht.le, ht'.le⟩
      refine ⟨ti, ?_⟩
      dsimp only
      have hleft := boundaryArc_interior L₁ w true ti ⟨ht, ht'⟩
      have hright : boundaryArc L₂ w (!true) ti = upper L₂ w (L₂.arc w ti) := by
        rw [Bool.not_true]
        exact boundaryArc_false L₂ w ti
      exact congrArg₂ Prod.mk (congrArg Sum.inl hleft) (congrArg Sum.inr hright)
    | initial =>
      left
      refine ⟨⟨0, by constructor <;> norm_num⟩, ?_⟩
      dsimp only
      rw [boundaryArc_zero, boundaryArc_zero]
    | terminal =>
      left
      refine ⟨⟨1, by constructor <;> norm_num⟩, ?_⟩
      dsimp only
      rw [boundaryArc_one, boundaryArc_one]

def identificationGraph (L₁ L₂ : Lattice) (w : Plane) :
    Set (Raw L₁ L₂ w × Raw L₁ L₂ w) :=
  forwardGraph L₁ L₂ w ∪ Prod.swap '' forwardGraph L₁ L₂ w

theorem identificationGraph_compact (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    IsCompact (identificationGraph L₁ L₂ w) := by
  have hG := (bankGraph_compact L₁ L₂ w hw₁ hw₂ false).union
    (bankGraph_compact L₁ L₂ w hw₁ hw₂ true)
  exact hG.union (hG.image continuous_swap)

theorem identificationGraph_mem_iff (L₁ L₂ : Lattice) (w : Plane) (p q : Raw L₁ L₂ w) :
    (p, q) ∈ identificationGraph L₁ L₂ w ↔
      SeamRelation L₁ L₂ w p q ∨ SeamRelation L₁ L₂ w q p := by
  have hswap : (p, q) ∈ Prod.swap '' forwardGraph L₁ L₂ w ↔
      (q, p) ∈ forwardGraph L₁ L₂ w := by
    constructor
    · rintro ⟨r, hr, heq⟩
      have h := congrArg Prod.swap heq
      simp only [Prod.swap_swap] at h
      change r = (q, p) at h
      rw [← h]
      exact hr
    · intro h
      exact ⟨(q, p), h, rfl⟩
  exact or_congr (forwardGraph_mem_iff L₁ L₂ w p q)
    (hswap.trans (forwardGraph_mem_iff L₁ L₂ w q p))

theorem glue_eq_or_identificationGraph (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (p q : Raw L₁ L₂ w) :
    glue L₁ L₂ w p = glue L₁ L₂ w q ↔ p = q ∨ (p, q) ∈ identificationGraph L₁ L₂ w := by
  rw [SeamClasses.glue_eq_iff L₁ L₂ w hw₁ hw₂, identificationGraph_mem_iff]

theorem isQuotientMap_glue (L₁ L₂ : Lattice) (w : Plane) : IsQuotientMap (glue L₁ L₂ w) :=
  isQuotientMap_quotient_mk'

theorem isClosedMap_glue (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) : IsClosedMap (glue L₁ L₂ w) := by
  let _ := cutT2Space L₁ w hw₁
  let _ := cutT2Space L₂ w hw₂
  exact isClosedMap_of_compact_identification _ (isQuotientMap_glue L₁ L₂ w)
    _ (identificationGraph_compact L₁ L₂ w hw₁ hw₂)
    (glue_eq_or_identificationGraph L₁ L₂ w hw₁ hw₂)

theorem isProperMap_glue (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) : IsProperMap (glue L₁ L₂ w) := by
  let _ := cutT2Space L₁ w hw₁
  let _ := cutT2Space L₂ w hw₂
  exact isProperMap_of_compact_identification _ (isQuotientMap_glue L₁ L₂ w)
    _ (identificationGraph_compact L₁ L₂ w hw₁ hw₂)
    (glue_eq_or_identificationGraph L₁ L₂ w hw₁ hw₂)

theorem surfaceT2Space (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) : T2Space (Surface L₁ L₂ w) := by
  let _ := cutT2Space L₁ w hw₁
  let _ := cutT2Space L₂ w hw₂
  exact t2Space_of_compact_identification _ (isQuotientMap_glue L₁ L₂ w)
    _ (identificationGraph_compact L₁ L₂ w hw₁ hw₂)
    (glue_eq_or_identificationGraph L₁ L₂ w hw₁ hw₂)

end MNEC.SlitQuotientSeparation
