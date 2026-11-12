module

public import MNEC.SlitConnectedSum
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Open torus pieces in the physical slit-gluing quotient

The complements of the physical slits embed openly in the independently
generated cut topologies and in the actual seam quotient. The explicit
physical frame is adapted from the user's previous geometric slit-coordinate
construction, with each torus now using its own arbitrary lattice projection.
No previous CriticalMeasure theorem or module is imported.
-/

noncomputable section

namespace MNEC.OffSlitEmbeddings

open LatticeTorus CutTorus SlitConnectedSum Set Topology
open scoped Classical

theorem embeddedSlit_ne_zero (L : Lattice) (w : Plane) (hw : L.EmbeddedSlit w) :
    w ≠ 0 := by
  intro hz
  have heq : L.arc w ⟨0, by constructor <;> norm_num⟩ =
      L.arc w ⟨1, by constructor <;> norm_num⟩ := by
    simp [Lattice.arc, hz]
  have h := congrArg Subtype.val (hw heq)
  norm_num at h

def frame (w : Plane) (p : Plane) : Plane := p.1 • w + p.2 • normal w

def frameDet (w : Plane) : ℝ := w.1 ^ 2 + w.2 ^ 2

def frameInverse (w : Plane) (p : Plane) : Plane :=
  ((w.1 * p.1 + w.2 * p.2) / frameDet w,
   (-w.2 * p.1 + w.1 * p.2) / frameDet w)

theorem frameDet_pos (w : Plane) (hw : w ≠ 0) : 0 < frameDet w := by
  have hx := sq_nonneg w.1
  have hy := sq_nonneg w.2
  unfold frameDet
  by_contra hn
  have heq : w.1 ^ 2 + w.2 ^ 2 = 0 :=
    le_antisymm (le_of_not_gt hn) (add_nonneg hx hy)
  have h₁ : w.1 = 0 := by nlinarith only [heq, hy]
  have h₂ : w.2 = 0 := by nlinarith only [heq, hx]
  exact hw (Prod.ext h₁ h₂)

theorem frameInverse_frame (w : Plane) (hw : w ≠ 0) (p : Plane) :
    frameInverse w (frame w p) = p := by
  have hD := (frameDet_pos w hw).ne'
  apply Prod.ext <;> dsimp [frameInverse, frame, normal]
  · apply (div_eq_iff hD).mpr
    unfold frameDet
    ring
  · apply (div_eq_iff hD).mpr
    unfold frameDet
    ring

theorem frame_frameInverse (w : Plane) (hw : w ≠ 0) (p : Plane) :
    frame w (frameInverse w p) = p := by
  have hD := (frameDet_pos w hw).ne'
  apply Prod.ext <;> dsimp [frameInverse, frame, normal]
  · field_simp
    unfold frameDet
    ring
  · field_simp
    unfold frameDet
    ring

theorem continuous_frame (w : Plane) : Continuous (frame w) := by
  exact (continuous_fst.smul continuous_const).add
    (continuous_snd.smul continuous_const)

theorem continuous_frameInverse (w : Plane) : Continuous (frameInverse w) := by
  exact (((continuous_const.mul continuous_fst).add
    (continuous_const.mul continuous_snd)).div_const _).prodMk
    (((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd)).div_const _)

def frameHomeomorph (w : Plane) (hw : w ≠ 0) : Plane ≃ₜ Plane where
  toFun := frame w
  invFun := frameInverse w
  left_inv := frameInverse_frame w hw
  right_inv := frame_frameInverse w hw
  continuous_toFun := continuous_frame w
  continuous_invFun := continuous_frameInverse w

def reflectNormal : Plane ≃ₜ Plane :=
  (Homeomorph.refl ℝ).prodCongr (Homeomorph.neg ℝ)

def signedFrameHomeomorph (w : Plane) (hw : w ≠ 0) (k : Bool) : Plane ≃ₜ Plane :=
  if k then reflectNormal.trans (frameHomeomorph w hw) else frameHomeomorph w hw

theorem signedFrame_apply (w : Plane) (hw : w ≠ 0) (k : Bool) (p : Plane) :
    signedFrameHomeomorph w hw k p = p.1 • w + (sideSign k * p.2) • normal w := by
  cases k <;> simp [signedFrameHomeomorph, sideSign, reflectNormal, frameHomeomorph, frame]

def signedStrip (L : Lattice) (w : Plane) (a b r : ℝ) (k : Bool) : Set Torus :=
  {p | ∃ s ∈ Ioo a b, ∃ t ∈ Ioo (0 : ℝ) r,
    L.project (s • w + (sideSign k * t) • normal w) = p}

theorem signedStrip_eq_image (L : Lattice) (w : Plane) (hw : w ≠ 0)
    (a b r : ℝ) (k : Bool) :
    signedStrip L w a b r k = L.project ''
      (signedFrameHomeomorph w hw k '' (Ioo a b ×ˢ Ioo (0 : ℝ) r)) := by
  ext p
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨signedFrameHomeomorph w hw k (s, t),
      ⟨(s, t), ⟨hs, ht⟩, rfl⟩, signedFrame_apply w hw k (s, t) ▸ rfl⟩
  · rintro ⟨q, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩, rfl⟩
    exact ⟨s, hs, t, ht, signedFrame_apply w hw k (s, t) ▸ rfl⟩

theorem signedStrip_open (L : Lattice) (w : Plane) (hw : w ≠ 0)
    (a b r : ℝ) (k : Bool) : IsOpen (signedStrip L w a b r k) := by
  rw [signedStrip_eq_image L w hw]
  exact L.isOpenMap_project _
    ((signedFrameHomeomorph w hw k).isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo))

def normalLift (L : Lattice) (w : Plane) (p : OffSlit L w) : Point L w := upper L w p

@[simp] theorem base_normalLift (L : Lattice) (w : Plane) (p : OffSlit L w) :
    base (normalLift L w p) = p := rfl

theorem preimage_bankNeighborhood_normalLift (L : Lattice) (w : Plane)
    (a b r : ℝ) (k : Bool) (ha : 0 < a) (hb : b < 1) :
    normalLift L w ⁻¹' bankNeighborhood L w a b r k =
      (Subtype.val : OffSlit L w → Torus) ⁻¹' signedStrip L w a b r k := by
  ext p
  constructor
  · intro h
    rcases h with ⟨_, hs⟩ | ⟨_, s, hs, heq⟩
    · exact hs
    · exact False.elim (p.property
        ⟨⟨s, (ha.trans hs.1).le, (hs.2.trans hb).le⟩, heq⟩)
  · intro h
    exact Or.inl ⟨p.property, h⟩

theorem continuous_normalLift (L : Lattice) (w : Plane) (hw : w ≠ 0) :
    Continuous (normalLift L w) := by
  apply continuous_generateFrom_iff.mpr
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩ | ⟨a, b, r, k, ha, _hab, hb, _hr, rfl⟩
  · exact hV.preimage continuous_subtype_val
  · rw [preimage_bankNeighborhood_normalLift L w a b r k ha hb]
    exact (signedStrip_open L w hw a b r k).preimage continuous_subtype_val

theorem normalLift_injective (L : Lattice) (w : Plane) :
    Function.Injective (normalLift L w) := by
  intro p q h
  exact Subtype.ext (congrArg base h)

theorem image_normalLift (L : Lattice) (w : Plane) (V : Set (OffSlit L w)) :
    normalLift L w '' V = base ⁻¹' ((Subtype.val : OffSlit L w → Torus) '' V) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, hbase⟩
    refine ⟨p, hp, ?_⟩
    apply point_ext (p := normalLift L w p) (q := q)
    · exact hbase
    · change false = bank q
      exact (bank_false_off_interior q (fun hi => p.property
        (hbase.symm ▸ interior_subset_slit L w hi))).symm

theorem isOpenMap_normalLift (L : Lattice) (w : Plane) : IsOpenMap (normalLift L w) := by
  intro V hV
  rw [image_normalLift]
  exact (((L.slitSet_closed w).isOpen_compl).isOpenMap_subtype_val V hV).preimage
    (continuous_base L w)

theorem isOpenEmbedding_normalLift (L : Lattice) (w : Plane) (hw : w ≠ 0) :
    IsOpenEmbedding (normalLift L w) :=
  .of_continuous_injective_isOpenMap (continuous_normalLift L w hw)
    (normalLift_injective L w) (isOpenMap_normalLift L w)

def rawOffSlit {L₁ L₂ : Lattice} {w : Plane} : Raw L₁ L₂ w → Prop
  | Sum.inl p => base p ∉ L₁.slitSet w
  | Sum.inr p => base p ∉ L₂.slitSet w

/-- An equivalence class containing an off-slit point is a singleton, proved
from the quotient invariant rather than assumed as a gluing property. -/
theorem related_eq_off_slit {L₁ L₂ : Lattice} {w : Plane} {p q : Raw L₁ L₂ w}
    (hq : rawOffSlit q)
    (hpq : Relation.EqvGen (SeamRelation L₁ L₂ w) p q) : p = q := by
  have ht := offLabel_related hpq
  cases p with
  | inl p =>
      cases q with
      | inl q =>
          change base q ∉ L₁.slitSet w at hq
          by_cases hp : base p ∈ L₁.slitSet w
          · simp [offLabel, hp, hq] at ht
          · have hb : base p = base q := by simpa [offLabel, hp, hq] using ht
            exact congrArg Sum.inl (point_ext hb
              ((bank_false_off_interior p (fun hi => hp (interior_subset_slit L₁ w hi))).trans
                (bank_false_off_interior q (fun hi => hq (interior_subset_slit L₁ w hi))).symm))
      | inr q =>
          change base q ∉ L₂.slitSet w at hq
          by_cases hp : base p ∈ L₁.slitSet w <;> simp [offLabel, hp, hq] at ht
  | inr p =>
      cases q with
      | inl q =>
          change base q ∉ L₁.slitSet w at hq
          by_cases hp : base p ∈ L₂.slitSet w <;> simp [offLabel, hp, hq] at ht
      | inr q =>
          change base q ∉ L₂.slitSet w at hq
          by_cases hp : base p ∈ L₂.slitSet w
          · simp [offLabel, hp, hq] at ht
          · have hb : base p = base q := by simpa [offLabel, hp, hq] using ht
            exact congrArg Sum.inr (point_ext hb
              ((bank_false_off_interior p (fun hi => hp (interior_subset_slit L₂ w hi))).trans
                (bank_false_off_interior q (fun hi => hq (interior_subset_slit L₂ w hi))).symm))

theorem preimage_image_glue_off_slit (L₁ L₂ : Lattice) (w : Plane)
    (S : Set (Raw L₁ L₂ w)) (hS : ∀ q ∈ S, rawOffSlit q) :
    glue L₁ L₂ w ⁻¹' (glue L₁ L₂ w '' S) = S := by
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    have hpq : Relation.EqvGen (SeamRelation L₁ L₂ w) p q :=
      Quotient.exact hqp.symm
    have heq := related_eq_off_slit (hS q hq) hpq
    simpa only [heq] using hq
  · exact fun hp => ⟨p, hp, rfl⟩

theorem continuous_leftOff (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    Continuous (leftOff L₁ L₂ w) :=
  (continuous_left L₁ L₂ w).comp (continuous_normalLift L₁ w hw)

theorem continuous_rightOff (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    Continuous (rightOff L₁ L₂ w) :=
  (continuous_right L₁ L₂ w).comp (continuous_normalLift L₂ w hw)

theorem isOpenMap_leftOff (L₁ L₂ : Lattice) (w : Plane) :
    IsOpenMap (leftOff L₁ L₂ w) := by
  intro V hV
  let rawMap : OffSlit L₁ w → Raw L₁ L₂ w := fun p => Sum.inl (normalLift L₁ w p)
  have hraw : IsOpen (rawMap '' V) :=
    (isOpenMap_inl.comp (isOpenMap_normalLift L₁ w)) V hV
  have hoff : ∀ q ∈ rawMap '' V, rawOffSlit q := by
    rintro q ⟨p, _, rfl⟩
    exact p.property
  have hpre : IsOpen (glue L₁ L₂ w ⁻¹' (glue L₁ L₂ w '' (rawMap '' V))) := by
    rw [preimage_image_glue_off_slit L₁ L₂ w _ hoff]
    exact hraw
  have hquot := (isQuotientMap_quotient_mk' (s := gluingSetoid L₁ L₂ w)).isCoinducing
  have hopen := hquot.isOpen_preimage.mp hpre
  have heq : glue L₁ L₂ w '' (rawMap '' V) = leftOff L₁ L₂ w '' V := by
    rw [← Set.image_comp]
    rfl
  exact heq ▸ hopen

theorem isOpenMap_rightOff (L₁ L₂ : Lattice) (w : Plane) :
    IsOpenMap (rightOff L₁ L₂ w) := by
  intro V hV
  let rawMap : OffSlit L₂ w → Raw L₁ L₂ w := fun p => Sum.inr (normalLift L₂ w p)
  have hraw : IsOpen (rawMap '' V) :=
    (isOpenMap_inr.comp (isOpenMap_normalLift L₂ w)) V hV
  have hoff : ∀ q ∈ rawMap '' V, rawOffSlit q := by
    rintro q ⟨p, _, rfl⟩
    exact p.property
  have hpre : IsOpen (glue L₁ L₂ w ⁻¹' (glue L₁ L₂ w '' (rawMap '' V))) := by
    rw [preimage_image_glue_off_slit L₁ L₂ w _ hoff]
    exact hraw
  have hquot := (isQuotientMap_quotient_mk' (s := gluingSetoid L₁ L₂ w)).isCoinducing
  have hopen := hquot.isOpen_preimage.mp hpre
  have heq : glue L₁ L₂ w '' (rawMap '' V) = rightOff L₁ L₂ w '' V := by
    rw [← Set.image_comp]
    rfl
  exact heq ▸ hopen

theorem isOpenEmbedding_leftOff (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    IsOpenEmbedding (leftOff L₁ L₂ w) :=
  .of_continuous_injective_isOpenMap (continuous_leftOff L₁ L₂ w hw)
    (leftOff_injective L₁ L₂ w) (isOpenMap_leftOff L₁ L₂ w)

theorem isOpenEmbedding_rightOff (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    IsOpenEmbedding (rightOff L₁ L₂ w) :=
  .of_continuous_injective_isOpenMap (continuous_rightOff L₁ L₂ w hw)
    (rightOff_injective L₁ L₂ w) (isOpenMap_rightOff L₁ L₂ w)

/-- The two open torus pieces are exactly the points with a nonempty
off-slit quotient label. -/
theorem union_off_ranges (L₁ L₂ : Lattice) (w : Plane) :
    range (leftOff L₁ L₂ w) ∪ range (rightOff L₁ L₂ w) =
      {p | offTrace L₁ L₂ w p ≠ none} := by
  ext p
  constructor
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · simp only [Set.mem_ofPred_eq, offTrace_leftOff, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [Set.mem_ofPred_eq, offTrace_rightOff, ne_eq, reduceCtorEq, not_false_eq_true]
  · refine Quotient.inductionOn p (fun raw => ?_)
    cases raw with
    | inl q =>
        intro hq
        have hoff : base q ∉ L₁.slitSet w := by
          intro h
          exact hq (by simp only [offTrace, Quotient.lift_mk, offLabel, ite_eq_left h])
        let x : OffSlit L₁ w := ⟨base q, hoff⟩
        have heq : upper L₁ w (base q) = q := by
          apply point_ext (p := upper L₁ w (base q)) (q := q) rfl
          exact (bank_false_off_interior q
            (fun hi => hoff (interior_subset_slit L₁ w hi))).symm
        apply Or.inl
        refine ⟨x, ?_⟩
        change left L₁ L₂ w (upper L₁ w (base q)) = left L₁ L₂ w q
        rw [heq]
    | inr q =>
        intro hq
        have hoff : base q ∉ L₂.slitSet w := by
          intro h
          exact hq (by simp only [offTrace, Quotient.lift_mk, offLabel, ite_eq_left h])
        let x : OffSlit L₂ w := ⟨base q, hoff⟩
        have heq : upper L₂ w (base q) = q := by
          apply point_ext (p := upper L₂ w (base q)) (q := q) rfl
          exact (bank_false_off_interior q
            (fun hi => hoff (interior_subset_slit L₂ w hi))).symm
        apply Or.inr
        refine ⟨x, ?_⟩
        change right L₁ L₂ w (upper L₂ w (base q)) = right L₁ L₂ w q
        rw [heq]

end MNEC.OffSlitEmbeddings
