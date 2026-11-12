module

public import MNEC.RegularAtlasCoverage
public import MNEC.OffSlitChartArea
public import MNEC.SeamChartArea

@[expose] public section

/-!
# The constructed regular atlas carries the actual flat area

Every physical chart, including those across the seam, sends each Borel
subset of its source to a set of exactly the same area. The proof uses the
computed quotient area and physical lattice projections.
-/

namespace MNEC.RegularAtlasArea

open LatticeTorus SlitConnectedSum RegularAtlasCoverage ConnectedSumArea MeasureTheory Set

theorem chart_image_measurable {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (V : Set Plane) (hV : MeasurableSet V)
    (hsub : V ⊆ (chart hw₁ hw₂ i).source) :
    MeasurableSet ((chart hw₁ hw₂ i) '' V) :=
  OffSlitChartArea.chart_image_measurable _ V hV hsub

theorem chart_image_area {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (V : Set Plane) (hV : MeasurableSet V)
    (hsub : V ⊆ (chart hw₁ hw₂ i).source) :
    area L₁ L₂ w ((chart hw₁ hw₂ i) '' V) = volume V := by
  cases i with
  | left a =>
      exact OffSlitChartArea.leftChart_area_image L₁ L₂ w
        (OffSlitEmbeddings.embeddedSlit_ne_zero L₁ w hw₁) a V hV hsub
  | right a =>
      exact OffSlitChartArea.rightChart_area_image L₁ L₂ w
        (OffSlitEmbeddings.embeddedSlit_ne_zero L₁ w hw₁) a V hV hsub
  | seam C k =>
      exact SeamChartArea.physicalChart_area_image hw₁ hw₂ C k V hV hsub

end MNEC.RegularAtlasArea
