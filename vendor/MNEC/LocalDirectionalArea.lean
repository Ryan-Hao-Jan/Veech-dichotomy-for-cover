module

public import MNEC.RegularAtlasArea
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section

/-!
# Actual local time maps preserve the independently constructed flat area

Each partial time map is the conjugate of a physical plane translation by
one proved regular chart. Its open source is stated explicitly, and area
preservation is derived from the actual chart-area identities and Lebesgue
translation invariance. A global flow is not assumed here.
-/

noncomputable section

namespace MNEC.LocalDirectionalArea

open LatticeTorus SlitConnectedSum RegularAtlasCoverage ConnectedSumArea MeasureTheory Set

def timeMap {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (t : ℝ) :
    OpenPartialHomeomorph (Surface L₁ L₂ w) (Surface L₁ L₂ w) :=
  (((chart hw₁ hw₂ i).symm).transHomeomorph (Homeomorph.addRight (t • v))).trans
    (chart hw₁ hw₂ i)

theorem timeMap_apply {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (t : ℝ) (x : Surface L₁ L₂ w) :
    timeMap hw₁ hw₂ i v t x =
      chart hw₁ hw₂ i ((chart hw₁ hw₂ i).symm x + t • v) := rfl

theorem mem_timeMap_source {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (t : ℝ) (x : Surface L₁ L₂ w) :
    x ∈ (timeMap hw₁ hw₂ i v t).source ↔
      x ∈ (chart hw₁ hw₂ i).target ∧
        (chart hw₁ hw₂ i).symm x + t • v ∈ (chart hw₁ hw₂ i).source := Iff.rfl

theorem volume_translation (a : Plane) (B : Set Plane) :
    volume ((fun p : Plane => p + a) '' B) = volume B := by
  let : Measure.IsAddRightInvariant (volume : Measure Plane) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let τ := Homeomorph.addRight a
  have h := (measurePreserving_add_right (volume : Measure Plane) a).measure_preimage_emb
    τ.toMeasurableEquiv.measurableEmbedding ((fun p : Plane => p + a) '' B)
  have hpre : (fun p : Plane => p + a) ⁻¹' ((fun p : Plane => p + a) '' B) = B :=
    Set.preimage_image_eq B τ.injective
  rw [hpre] at h
  exact h.symm

theorem timeMap_image_measurable {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (t : ℝ) (V : Set (Surface L₁ L₂ w))
    (hV : MeasurableSet V) (hsub : V ⊆ (timeMap hw₁ hw₂ i v t).source) :
    MeasurableSet (timeMap hw₁ hw₂ i v t '' V) :=
  OffSlitChartArea.chart_image_measurable _ V hV hsub

theorem timeMap_image_area {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (t : ℝ) (V : Set (Surface L₁ L₂ w))
    (hV : MeasurableSet V) (hsub : V ⊆ (timeMap hw₁ hw₂ i v t).source) :
    area L₁ L₂ w (timeMap hw₁ hw₂ i v t '' V) = area L₁ L₂ w V := by
  let e := chart hw₁ hw₂ i
  let B : Set Plane := e.symm '' V
  let D : Set Plane := (fun p : Plane => p + t • v) '' B
  have htarget : V ⊆ e.target := by
    intro x hx
    exact ((mem_timeMap_source hw₁ hw₂ i v t x).mp (hsub hx)).1
  have hB : MeasurableSet B := OffSlitChartArea.chart_image_measurable e.symm V hV htarget
  have hBsource : B ⊆ e.source := by
    rintro p ⟨x, hx, rfl⟩
    exact e.map_target (htarget hx)
  have hD : MeasurableSet D :=
    OffSlitChartArea.chart_image_measurable (Homeomorph.addRight (t • v)).toOpenPartialHomeomorph
      B hB (Set.subset_univ _)
  have hDsource : D ⊆ e.source := by
    rintro p ⟨b, ⟨x, hx, hxb⟩, rfl⟩
    rw [← hxb]
    exact ((mem_timeMap_source hw₁ hw₂ i v t x).mp (hsub hx)).2
  have himage : timeMap hw₁ hw₂ i v t '' V = e '' D := by
    change (fun x => e (e.symm x + t • v)) '' V =
      e '' ((fun p : Plane => p + t • v) '' (e.symm '' V))
    rw [Set.image_image, Set.image_image]
  have hinverse : e '' B = V := e.image_symm_image_of_subset_target htarget
  calc
    area L₁ L₂ w (timeMap hw₁ hw₂ i v t '' V) = area L₁ L₂ w (e '' D) :=
      congrArg (area L₁ L₂ w) himage
    _ = volume D := RegularAtlasArea.chart_image_area hw₁ hw₂ i D hD hDsource
    _ = volume B := volume_translation (t • v) B
    _ = area L₁ L₂ w (e '' B) :=
      (RegularAtlasArea.chart_image_area hw₁ hw₂ i B hB hBsource).symm
    _ = area L₁ L₂ w V := congrArg (area L₁ L₂ w) hinverse

end MNEC.LocalDirectionalArea
