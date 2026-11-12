module

public import MNEC.RegularAtlasArea
public import MNEC.RegularTopologyArea
public import MNEC.LocalDirectionalArea

@[expose] public section

/-!
# Physical chart area on the actual regular subtype

The subtype measure is pulled back from the independently constructed
surface area. Actual inverse regular charts have the same physical-plane
area by the proved subtype-coordinate formula. A general conjugated
translation then preserves that area on its actual partial-map source.
-/

noncomputable section

namespace MNEC.RegularCoordinateArea

open LatticeTorus SlitConnectedSum RegularChartedSpace RegularAtlasCoverage RegularAtlasArea
open RegularPoints RegularTopologyArea ConnectedSumArea MeasureTheory Set Topology
open scoped ENNReal Classical

def regularModel {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : RegularAtlasCoverage.Index L₁ L₂ w) : OpenPartialHomeomorph Plane (Regular L₁ L₂ w) :=
  (regularChart hw₁ hw₂ i).symm

theorem regularModel_source {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : RegularAtlasCoverage.Index L₁ L₂ w) :
    (regularModel hw₁ hw₂ i).source = (RegularAtlasCoverage.chart hw₁ hw₂ i).source :=
  regularChart_target hw₁ hw₂ i

theorem regularModel_apply_val {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : RegularAtlasCoverage.Index L₁ L₂ w) (p : Plane)
    (hp : p ∈ (regularModel hw₁ hw₂ i).source) :
    (regularModel hw₁ hw₂ i p).val = RegularAtlasCoverage.chart hw₁ hw₂ i p :=
  (RegularAtlasCoverage.chart hw₁ hw₂ i).symm.subtypeRestr_symm_apply
    (regular_nonempty L₁ L₂ w) hp

theorem regularModel_area_image {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : RegularAtlasCoverage.Index L₁ L₂ w) (V : Set Plane) (hV : MeasurableSet V)
    (hsub : V ⊆ (regularModel hw₁ hw₂ i).source) :
    regularArea L₁ L₂ w (regularModel hw₁ hw₂ i '' V) = volume V := by
  rw [regularArea, comap_subtype_coe_apply (regularSet_open hw₁ hw₂).measurableSet,
    Set.image_image]
  have himage : (fun p => (regularModel hw₁ hw₂ i p).val) '' V =
      RegularAtlasCoverage.chart hw₁ hw₂ i '' V :=
    Set.image_congr fun p hp => regularModel_apply_val hw₁ hw₂ i p (hsub hp)
  rw [himage]
  apply chart_image_area hw₁ hw₂ i V hV
  exact hsub.trans (by rw [regularModel_source])

section Translation

variable {X : Type*} [TopologicalSpace X]

def translationTimeMap (e : OpenPartialHomeomorph Plane X) (v : Plane) (t : ℝ) :
    OpenPartialHomeomorph X X :=
  (e.symm.transHomeomorph (Homeomorph.addRight (t • v))).trans e

theorem translationTimeMap_apply (e : OpenPartialHomeomorph Plane X) (v : Plane) (t : ℝ) (x : X) :
    translationTimeMap e v t x = e (e.symm x + t • v) := rfl

theorem mem_translationTimeMap_source (e : OpenPartialHomeomorph Plane X) (v : Plane) (t : ℝ) (x : X) :
    x ∈ (translationTimeMap e v t).source ↔
      x ∈ e.target ∧ e.symm x + t • v ∈ e.source := Iff.rfl

variable [MeasurableSpace X] [BorelSpace X]

theorem translationTimeMap_image_area (μ : Measure X) (e : OpenPartialHomeomorph Plane X)
    (hchart : ∀ (V : Set Plane), MeasurableSet V → V ⊆ e.source → μ (e '' V) = volume V)
    (v : Plane) (t : ℝ) (V : Set X) (hV : MeasurableSet V)
    (hsub : V ⊆ (translationTimeMap e v t).source) :
    μ (translationTimeMap e v t '' V) = μ V := by
  let B : Set Plane := e.symm '' V
  let D : Set Plane := (fun p : Plane => p + t • v) '' B
  have htarget : V ⊆ e.target := fun x hx =>
    ((mem_translationTimeMap_source e v t x).mp (hsub hx)).1
  have hB : MeasurableSet B := OffSlitChartArea.chart_image_measurable e.symm V hV htarget
  have hBsource : B ⊆ e.source := by
    rintro p ⟨x, hx, rfl⟩
    exact e.map_target (htarget hx)
  have hD : MeasurableSet D := OffSlitChartArea.chart_image_measurable
    (Homeomorph.addRight (t • v)).toOpenPartialHomeomorph B hB (subset_univ _)
  have hDsource : D ⊆ e.source := by
    rintro p ⟨b, ⟨x, hx, hxb⟩, rfl⟩
    rw [← hxb]
    exact ((mem_translationTimeMap_source e v t x).mp (hsub hx)).2
  have himage : translationTimeMap e v t '' V = e '' D := by
    change (fun x => e (e.symm x + t • v)) '' V =
      e '' ((fun p : Plane => p + t • v) '' (e.symm '' V))
    rw [Set.image_image, Set.image_image]
  have hinverse : e '' B = V := e.image_symm_image_of_subset_target htarget
  calc
    μ (translationTimeMap e v t '' V) = μ (e '' D) := congrArg μ himage
    _ = volume D := hchart D hD hDsource
    _ = volume B := LocalDirectionalArea.volume_translation (t • v) B
    _ = μ (e '' B) := (hchart B hB hBsource).symm
    _ = μ V := congrArg μ hinverse

end Translation

end MNEC.RegularCoordinateArea
