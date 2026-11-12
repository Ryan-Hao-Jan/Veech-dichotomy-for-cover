module

public import MNEC.SeamChartMaps

/-!
# Open images of seam charts away from their axes

The sign-restricted coordinate images are open in the physical plane,
their actual lattice projections are open, and the off-slit inclusions
into the cross-glued quotient are open. This proves local openness without
assuming that the seam rectangle map is a homeomorphism.
-/

noncomputable section
@[expose] public section

namespace MNEC.SeamChartOffAxis

open LatticeTorus CutTorus OffSlitEmbeddings SlitCollars CutBankLifts SlitConnectedSum
open SeamChartMaps Set Topology
open scoped Classical

theorem signed_position_mem {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) :
    (q.val.1, sideSign k * q.val.2) ∈ rectangle C.a C.b C.r := by
  cases k with
  | false => simp [sideSign]
  | true =>
    refine ⟨q.property.1, ?_⟩
    simp only [sideSign, ite_true, neg_one_mul]
    exact ⟨by linarith only [q.property.2.2], by linarith only [q.property.2.1]⟩

theorem signedFrame_eq_frame (w : Plane) (hw : w ≠ 0) (k : Bool) (p : Plane) :
    signedFrameHomeomorph w hw k p = frame w (p.1, sideSign k * p.2) := by
  rw [signedFrame_apply]
  rfl

theorem left_signed_projection_off_slit {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (hw : w ≠ 0) (k : Bool) (q : Domain C)
    (hq : q.val.2 ≠ 0) :
    L₁.project (signedFrameHomeomorph w hw k q.val) ∉ L₁.slitSet w := by
  rw [signedFrame_eq_frame]
  intro hslit
  have hzero := (C.left_slit_iff _ (signed_position_mem C k q)).1 hslit
  change sideSign k * q.val.2 = 0 at hzero
  cases k <;> exact hq (by simpa [sideSign] using hzero)

theorem right_signed_projection_off_slit {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (hw : w ≠ 0) (k : Bool) (q : Domain C)
    (hq : q.val.2 ≠ 0) :
    L₂.project (signedFrameHomeomorph w hw k q.val) ∉ L₂.slitSet w := by
  rw [signedFrame_eq_frame]
  intro hslit
  have hzero := (C.right_slit_iff _ (signed_position_mem C k q)).1 hslit
  change sideSign k * q.val.2 = 0 at hzero
  cases k <;> exact hq (by simpa [sideSign] using hzero)

theorem chart_positive_off {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (hw : w ≠ 0) (k : Bool) (q : Domain C)
    (hq : 0 < q.val.2) :
    chart C k q = leftOff L₁ L₂ w
      ⟨L₁.project (signedFrameHomeomorph w hw k q.val),
        left_signed_projection_off_slit C hw k q (ne_of_gt hq)⟩ := by
  rw [chart_positive C k q hq.le]
  unfold positiveExtension
  rw [halfLift_nonzero C.leftCollar k (leftAbsHalf C q) (abs_ne_zero.mpr (ne_of_gt hq))]
  have hbase : halfBase k (leftAbsHalf C q) =
      L₁.project (signedFrameHomeomorph w hw k q.val) := by
    rw [signedFrame_eq_frame]
    change L₁.project (frame w (q.val.1, sideSign k * |q.val.2|)) = _
    rw [abs_of_pos hq]
  change left L₁ L₂ w (upper L₁ w (halfBase k (leftAbsHalf C q))) =
    left L₁ L₂ w (upper L₁ w (L₁.project (signedFrameHomeomorph w hw k q.val)))
  rw [hbase]

theorem chart_negative_off {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (hw : w ≠ 0) (k : Bool) (q : Domain C)
    (hq : q.val.2 < 0) :
    chart C k q = rightOff L₁ L₂ w
      ⟨L₂.project (signedFrameHomeomorph w hw k q.val),
        right_signed_projection_off_slit C hw k q (ne_of_lt hq)⟩ := by
  rw [chart_negative C k q hq]
  unfold negativeExtension
  rw [halfLift_nonzero C.rightCollar (!k) (rightAbsHalf C q) (abs_ne_zero.mpr (ne_of_lt hq))]
  have hbase : halfBase (!k) (rightAbsHalf C q) =
      L₂.project (signedFrameHomeomorph w hw k q.val) := by
    rw [signedFrame_eq_frame]
    change L₂.project (frame w (q.val.1, sideSign (!k) * |q.val.2|)) = _
    rw [abs_of_neg hq]
    cases k <;> simp [sideSign]
  change right L₁ L₂ w (upper L₂ w (halfBase (!k) (rightAbsHalf C q))) =
    right L₁ L₂ w (upper L₂ w (L₂.project (signedFrameHomeomorph w hw k q.val)))
  rw [hbase]

theorem isOpen_chart_image_positive {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (C : CommonCollar L₁ L₂ w) (k : Bool)
    (V : Set (Domain C)) (hV : IsOpen V) :
    IsOpen (chart C k '' (V ∩ {q | 0 < q.val.2})) := by
  let hw : w ≠ 0 := embeddedSlit_ne_zero L₁ w hw₁
  let H := signedFrameHomeomorph w hw k
  let S : Set (Domain C) := V ∩ {q | 0 < q.val.2}
  have hS : IsOpen S := hV.inter (isOpen_Ioi.preimage continuous_subtype_val.snd)
  have hcoordinate : IsOpen ((Subtype.val : Domain C → Plane) '' S) :=
    (domain_open C.leftCollar).isOpenMap_subtype_val S hS
  let W : Set Torus := L₁.project '' (H '' ((Subtype.val : Domain C → Plane) '' S))
  have hW : IsOpen W := L₁.isOpenMap_project _ (H.isOpenMap _ hcoordinate)
  let T : Set (OffSlit L₁ w) := (Subtype.val : OffSlit L₁ w → Torus) ⁻¹' W
  have hT : IsOpen T := hW.preimage continuous_subtype_val
  have heq : chart C k '' S = leftOff L₁ L₂ w '' T := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      let qo : OffSlit L₁ w :=
        ⟨L₁.project (H q.val), left_signed_projection_off_slit C hw k q (ne_of_gt hq.2)⟩
      refine ⟨qo, ?_, ?_⟩
      · exact ⟨H q.val, ⟨q.val, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
      · exact (chart_positive_off C hw k q hq.2).symm
    · rintro ⟨qo, hqo, rfl⟩
      rcases hqo with ⟨p, ⟨v, ⟨q, hq, rfl⟩, rfl⟩, hp⟩
      refine ⟨q, hq, ?_⟩
      exact (chart_positive_off C hw k q hq.2).trans
        (congrArg (leftOff L₁ L₂ w) (Subtype.ext hp))
  change IsOpen (chart C k '' S)
  rw [heq]
  exact isOpenMap_leftOff L₁ L₂ w T hT

theorem isOpen_chart_image_negative {L₁ L₂ : Lattice} {w : Plane}
    (hw₂ : L₂.EmbeddedSlit w) (C : CommonCollar L₁ L₂ w) (k : Bool)
    (V : Set (Domain C)) (hV : IsOpen V) :
    IsOpen (chart C k '' (V ∩ {q | q.val.2 < 0})) := by
  let hw : w ≠ 0 := embeddedSlit_ne_zero L₂ w hw₂
  let H := signedFrameHomeomorph w hw k
  let S : Set (Domain C) := V ∩ {q | q.val.2 < 0}
  have hS : IsOpen S := hV.inter (isOpen_Iio.preimage continuous_subtype_val.snd)
  have hcoordinate : IsOpen ((Subtype.val : Domain C → Plane) '' S) :=
    (domain_open C.rightCollar).isOpenMap_subtype_val S hS
  let W : Set Torus := L₂.project '' (H '' ((Subtype.val : Domain C → Plane) '' S))
  have hW : IsOpen W := L₂.isOpenMap_project _ (H.isOpenMap _ hcoordinate)
  let T : Set (OffSlit L₂ w) := (Subtype.val : OffSlit L₂ w → Torus) ⁻¹' W
  have hT : IsOpen T := hW.preimage continuous_subtype_val
  have heq : chart C k '' S = rightOff L₁ L₂ w '' T := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      let qo : OffSlit L₂ w :=
        ⟨L₂.project (H q.val), right_signed_projection_off_slit C hw k q (ne_of_lt hq.2)⟩
      refine ⟨qo, ?_, ?_⟩
      · exact ⟨H q.val, ⟨q.val, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
      · exact (chart_negative_off C hw k q hq.2).symm
    · rintro ⟨qo, hqo, rfl⟩
      rcases hqo with ⟨p, ⟨v, ⟨q, hq, rfl⟩, rfl⟩, hp⟩
      refine ⟨q, hq, ?_⟩
      exact (chart_negative_off C hw k q hq.2).trans
        (congrArg (rightOff L₁ L₂ w) (Subtype.ext hp))
  change IsOpen (chart C k '' S)
  rw [heq]
  exact isOpenMap_rightOff L₁ L₂ w T hT

theorem exists_open_image_neighborhood_of_ne_zero {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (V : Set (Domain C)) (hV : IsOpen V)
    (q : Domain C) (hqV : q ∈ V) (hne : q.val.2 ≠ 0) :
    ∃ O : Set (Surface L₁ L₂ w), IsOpen O ∧ chart C k q ∈ O ∧ O ⊆ chart C k '' V := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨chart C k '' (V ∩ {q | q.val.2 < 0}),
      isOpen_chart_image_negative hw₂ C k V hV, ⟨q, ⟨hqV, hneg⟩, rfl⟩, ?_⟩
    exact Set.image_mono Set.inter_subset_left
  · refine ⟨chart C k '' (V ∩ {q | 0 < q.val.2}),
      isOpen_chart_image_positive hw₁ C k V hV, ⟨q, ⟨hqV, hpos⟩, rfl⟩, ?_⟩
    exact Set.image_mono Set.inter_subset_left

end MNEC.SeamChartOffAxis
