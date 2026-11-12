module

public import MNEC.RegularAtlasCoverage
public import Mathlib.Geometry.Manifold.ChartedSpace

@[expose] public section

/-!
# The independently constructed regular quotient as a charted space

Every chart is the restriction of a constructed physical open partial
homeomorphism. Its coverage follows from the proved classification of the
quotient points. No chart or manifold existence is supplied as a premise.
Smooth/translation compatibility is an additional theorem, kept separate
from this topological construction.
-/

noncomputable section

namespace MNEC.RegularChartedSpace

open LatticeTorus SlitConnectedSum RegularPoints RegularAtlasCoverage Set Topology
open scoped Classical

abbrev Regular (L₁ L₂ : Lattice) (w : Plane) := ↥(regularSet L₁ L₂ w)

theorem regular_nonempty (L₁ L₂ : Lattice) (w : Plane) : Nonempty (Regular L₁ L₂ w) := by
  obtain ⟨p⟩ := OffSlitCharts.offOpen_nonempty L₁ w
  exact ⟨⟨leftOff L₁ L₂ w p, leftOff_mem_regular L₁ L₂ w p⟩⟩

abbrev regularOpen {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    TopologicalSpace.Opens (Surface L₁ L₂ w) :=
  ⟨regularSet L₁ L₂ w, regularSet_open hw₁ hw₂⟩

def regularChart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w) :
    OpenPartialHomeomorph (Regular L₁ L₂ w) Plane :=
  (RegularAtlasCoverage.chart hw₁ hw₂ i).symm.subtypeRestr
    (s := regularOpen hw₁ hw₂) (regular_nonempty L₁ L₂ w)

theorem regularChart_source {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w) :
    (regularChart hw₁ hw₂ i).source =
      Subtype.val ⁻¹' (RegularAtlasCoverage.chart hw₁ hw₂ i).target := by
  simp only [regularChart, OpenPartialHomeomorph.subtypeRestr_source,
    OpenPartialHomeomorph.symm_source]
  rfl

theorem regularChart_apply {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w)
    (p : Regular L₁ L₂ w) :
    regularChart hw₁ hw₂ i p = (RegularAtlasCoverage.chart hw₁ hw₂ i).symm p.val := rfl

theorem regularChart_target {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w) :
    (regularChart hw₁ hw₂ i).target = (RegularAtlasCoverage.chart hw₁ hw₂ i).source := by
  apply Set.Subset.antisymm
  · exact (RegularAtlasCoverage.chart hw₁ hw₂ i).symm.subtypeRestr_target_subset _
  · intro q hq
    let e := (RegularAtlasCoverage.chart hw₁ hw₂ i).symm
    have hx : e.symm q ∈ regularSet L₁ L₂ w :=
      chart_target_subset_regular hw₁ hw₂ i ((RegularAtlasCoverage.chart hw₁ hw₂ i).map_source hq)
    let x : Regular L₁ L₂ w := ⟨e.symm q, hx⟩
    have hxsource : (x : Surface L₁ L₂ w) ∈ e.source := e.map_target hq
    have hmem := e.map_subtype_source (s := regularOpen hw₁ hw₂)
      (regular_nonempty L₁ L₂ w) (x := x) hxsource
    have heq : e x = q := e.right_inv hq
    rw [heq] at hmem
    exact hmem

def chosenIndex {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (p : Regular L₁ L₂ w) : Index L₁ L₂ w :=
  (chart_cover_regular hw₁ hw₂ p.val p.property).choose

theorem chosenIndex_mem_target {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (p : Regular L₁ L₂ w) :
    p.val ∈ (RegularAtlasCoverage.chart hw₁ hw₂ (chosenIndex hw₁ hw₂ p)).target :=
  (chart_cover_regular hw₁ hw₂ p.val p.property).choose_spec

@[instance_reducible] def chartedSpace {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    ChartedSpace Plane (Regular L₁ L₂ w) where
  atlas := range (regularChart hw₁ hw₂)
  chartAt p := regularChart hw₁ hw₂ (chosenIndex hw₁ hw₂ p)
  mem_chart_source p := by
    rw [regularChart_source]
    exact chosenIndex_mem_target hw₁ hw₂ p
  chart_mem_atlas p := ⟨chosenIndex hw₁ hw₂ p, rfl⟩

theorem locallyCompactRegular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    LocallyCompactSpace (Regular L₁ L₂ w) := by
  let := chartedSpace hw₁ hw₂
  exact ChartedSpace.locallyCompactSpace (H := Plane) (M := Regular L₁ L₂ w)

theorem locallyPathConnectedRegular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    LocallyPathConnectedSpace (Regular L₁ L₂ w) := by
  let := chartedSpace hw₁ hw₂
  exact ChartedSpace.locallyPathConnectedSpace (H := Plane) (M := Regular L₁ L₂ w)

end MNEC.RegularChartedSpace
