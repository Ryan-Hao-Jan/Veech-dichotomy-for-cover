module

public import MNEC.SeamChartCoordinates
public import MNEC.InjectiveTorusArea

@[expose] public section

/-!
# Proved physical area in the constructed seam charts

The positive and negative physical slices enter the two actual open torus
pieces. Their projections are injective because the seam chart is injective.
The physical axis and its image in the quotient seam both have zero area.
Finite additivity therefore identifies quotient area with planar Lebesgue
area throughout every constructed physical seam chart.
-/

noncomputable section

namespace MNEC.SeamChartArea

open LatticeTorus CutTorus SlitConnectedSum OffSlitEmbeddings SlitCollars
open CutBankLifts SeamChartMaps SeamChartOffAxis SeamCharts SeamChartCoordinates
open ConnectedSumArea OffSlitChartArea InjectiveTorusArea MeasureTheory Set Topology Function
open scoped ENNReal Classical

theorem disjoint_images_of_injOn {A B : Type*} (F : A → B) (U S T : Set A)
    (hinj : InjOn F U) (hS : S ⊆ U) (hT : T ⊆ U) (hdisj : Disjoint S T) :
    Disjoint (F '' S) (F '' T) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
  have hxy := hinj (hS hx) (hT hy) (hxp.trans hyp.symm)
  subst y
  exact Set.disjoint_left.mp hdisj hx hy

/-- Transfer the proved area of an open torus piece through a physical
projection formula on any measurable injective physical subset. -/
theorem projected_piece_area {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (L : Lattice) (w : Plane) (f : OffSlit L w → Y) (F : Plane → Y)
    (harea : ∀ T : Set (OffSlit L w), μ (f '' T) = offArea L w T)
    (S : Set Plane) (hS : MeasurableSet S) (hinj : InjOn L.project S)
    (hoff : ∀ p ∈ S, L.project p ∉ L.slitSet w)
    (hformula : ∀ p (hp : p ∈ S), F p = f ⟨L.project p, hoff p hp⟩) :
    μ (F '' S) = volume S := by
  let T : Set (OffSlit L w) := Subtype.val ⁻¹' (L.project '' S)
  have hval : Subtype.val '' T = L.project '' S := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨L.project p, hoff p hp⟩, ⟨p, hp, rfl⟩, rfl⟩
  have himage : F '' S = f '' T := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨L.project p, hoff p hp⟩, ⟨p, hp, rfl⟩, (hformula p hp).symm⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨p, hp, heq⟩ := hr
      refine ⟨p, hp, ?_⟩
      exact (hformula p hp).trans (congrArg f (Subtype.ext heq))
  rw [himage, harea, offArea,
    comap_subtype_coe_apply (L.slitSet_closed w).measurableSet.compl, hval]
  exact area_project_image_eq_of_injOn L S hS hinj

def height {L₁ : Lattice} {w : Plane} (hw₁ : L₁.EmbeddedSlit w)
    (k : Bool) (p : Plane) : ℝ := (coordinates hw₁ k p).2

theorem continuous_height {L₁ : Lattice} {w : Plane} (hw₁ : L₁.EmbeddedSlit w)
    (k : Bool) : Continuous (height hw₁ k) :=
  continuous_snd.comp (signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k).symm.continuous

theorem positive_project_off_slit {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source) (hpos : 0 < height hw₁ k p) :
    L₁.project p ∉ L₁.slitSet w := by
  have h := left_signed_projection_off_slit C (embeddedSlit_ne_zero L₁ w hw₁) k
    ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩ (ne_of_gt hpos)
  simpa only [coordinates, Homeomorph.apply_symm_apply] using h

theorem negative_project_off_slit {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ (physicalChart hw₁ hw₂ C k).source) (hneg : height hw₁ k p < 0) :
    L₂.project p ∉ L₂.slitSet w := by
  have h := right_signed_projection_off_slit C (embeddedSlit_ne_zero L₁ w hw₁) k
    ⟨coordinates hw₁ k p, coordinates_mem hw₁ hw₂ C k p hp⟩ (ne_of_lt hneg)
  simpa only [coordinates, Homeomorph.apply_symm_apply] using h

theorem physical_axis_volume_zero {L₁ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (k : Bool) : volume {p | height hw₁ k p = 0} = 0 := by
  apply measure_mono_null (t := affineLine 0 w)
  · intro p hp
    rw [physical_axis_position hw₁ k p hp]
    dsimp [affineLine]
    ring
  · exact affineLine_volume_zero 0 w (embeddedSlit_ne_zero L₁ w hw₁)

theorem physical_axis_image_area_zero {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (S : Set Plane)
    (hsub : S ⊆ (physicalChart hw₁ hw₂ C k).source)
    (hzero : ∀ p ∈ S, height hw₁ k p = 0) :
    area L₁ L₂ w (physicalChart hw₁ hw₂ C k '' S) = 0 := by
  apply measure_mono_null (t := seam L₁ L₂ w)
  · rintro q ⟨p, hp, rfl⟩
    have ht := (offTrace_physicalChart_eq_none_iff hw₁ hw₂ C k p (hsub hp)).2 (hzero p hp)
    change physicalChart hw₁ hw₂ C k p ∉
      range (leftOff L₁ L₂ w) ∪ range (rightOff L₁ L₂ w)
    rw [union_off_ranges]
    change ¬ offTrace L₁ L₂ w (physicalChart hw₁ hw₂ C k p) ≠ none
    exact fun hn => hn ht
  · exact seam_area_zero L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁)

theorem measurableSet_physicalChart_image {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (V : Set Plane) (hV : MeasurableSet V)
    (hsub : V ⊆ (physicalChart hw₁ hw₂ C k).source) :
    MeasurableSet (physicalChart hw₁ hw₂ C k '' V) :=
  chart_image_measurable _ V hV hsub

/-- Exact equality of quotient area with planar Lebesgue area for every
measurable subset of every actual physical seam chart domain. -/
theorem physicalChart_area_image {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (V : Set Plane) (hV : MeasurableSet V)
    (hsub : V ⊆ (physicalChart hw₁ hw₂ C k).source) :
    area L₁ L₂ w (physicalChart hw₁ hw₂ C k '' V) = volume V := by
  let e := physicalChart hw₁ hw₂ C k
  let P := V ∩ {p | 0 < height hw₁ k p}
  let N := V ∩ {p | height hw₁ k p < 0}
  let Z := V ∩ {p | height hw₁ k p = 0}
  have hP : MeasurableSet P := hV.inter (isOpen_lt continuous_const (continuous_height hw₁ k)).measurableSet
  have hN : MeasurableSet N := hV.inter (isOpen_lt (continuous_height hw₁ k) continuous_const).measurableSet
  have hZ : MeasurableSet Z := hV.inter
    (measurableSet_eq_fun (continuous_height hw₁ k).measurable measurable_const)
  have hPV : P ⊆ V := inter_subset_left
  have hNV : N ⊆ V := inter_subset_left
  have hZV : Z ⊆ V := inter_subset_left
  have hpart : V = P ∪ N ∪ Z := by
    ext p
    constructor
    · intro hp
      rcases lt_trichotomy (height hw₁ k p) 0 with hn | hz | hp'
      · exact Or.inl (Or.inr ⟨hp, hn⟩)
      · exact Or.inr ⟨hp, hz⟩
      · exact Or.inl (Or.inl ⟨hp, hp'⟩)
    · rintro ((hp | hp) | hp) <;> exact hp.1
  have hPN : Disjoint P N := by
    apply Set.disjoint_left.mpr
    intro p hp hn
    have hp' : 0 < height hw₁ k p := hp.2
    have hn' : height hw₁ k p < 0 := hn.2
    exact lt_asymm hp' hn'
  have hPNZ : Disjoint (P ∪ N) Z := by
    apply Set.disjoint_left.mpr
    rintro p (hp | hn) hz
    · exact hp.2.ne' hz.2
    · exact hn.2.ne hz.2
  have hareaP : area L₁ L₂ w (e '' P) = volume P := by
    apply projected_piece_area (area L₁ L₂ w) L₁ w (leftOff L₁ L₂ w) e
      (area_image_leftOff L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁)) P hP
    · intro p hp q hq heq
      apply e.injOn (hsub hp.1) (hsub hq.1)
      rw [physicalChart_positive hw₁ hw₂ C k p (hsub hp.1) hp.2,
        physicalChart_positive hw₁ hw₂ C k q (hsub hq.1) hq.2, heq]
    · intro p hp
      exact physicalChart_positive hw₁ hw₂ C k p (hsub hp.1) hp.2
    · intro p hp
      exact positive_project_off_slit hw₁ hw₂ C k p (hsub hp.1) hp.2
  have hareaN : area L₁ L₂ w (e '' N) = volume N := by
    apply projected_piece_area (area L₁ L₂ w) L₂ w (rightOff L₁ L₂ w) e
      (area_image_rightOff L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁)) N hN
    · intro p hp q hq heq
      apply e.injOn (hsub hp.1) (hsub hq.1)
      rw [physicalChart_negative hw₁ hw₂ C k p (hsub hp.1) hp.2,
        physicalChart_negative hw₁ hw₂ C k q (hsub hq.1) hq.2, heq]
    · intro p hp
      exact physicalChart_negative hw₁ hw₂ C k p (hsub hp.1) hp.2
    · intro p hp
      exact negative_project_off_slit hw₁ hw₂ C k p (hsub hp.1) hp.2
  have hareaZ : area L₁ L₂ w (e '' Z) = 0 :=
    physical_axis_image_area_zero hw₁ hw₂ C k Z (hZV.trans hsub) (fun _ hp => hp.2)
  have hvolZ : volume Z = 0 :=
    measure_mono_null inter_subset_right (physical_axis_volume_zero hw₁ k)
  have heP : MeasurableSet (e '' P) := chart_image_measurable e P hP (hPV.trans hsub)
  have heN : MeasurableSet (e '' N) := chart_image_measurable e N hN (hNV.trans hsub)
  have heZ : MeasurableSet (e '' Z) := chart_image_measurable e Z hZ (hZV.trans hsub)
  have hePN := disjoint_images_of_injOn e V P N (e.injOn.mono hsub) hPV hNV hPN
  have hePNZ : Disjoint (e '' P ∪ e '' N) (e '' Z) := by
    rw [← Set.image_union]
    exact disjoint_images_of_injOn e V (P ∪ N) Z (e.injOn.mono hsub)
      (union_subset hPV hNV) hZV hPNZ
  change area L₁ L₂ w (e '' V) = volume V
  rw [hpart, Set.image_union, Set.image_union,
    measure_union hePNZ heZ, measure_union hePN heN,
    hareaP, hareaN, hareaZ, add_zero,
    measure_union hPNZ hZ, measure_union hPN hN, hvolZ, add_zero]

end MNEC.SeamChartArea
