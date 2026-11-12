module

public import MNEC.RegularChartedSpace
public import MNEC.CutTorusBoundary
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

/-!
# Sigma compactness and second countability of the actual regular locus

The regular space is the continuous image of the disjoint union of the two
off-slit torus pieces and two open intervals parameterizing its seam banks.
This proves sigma compactness independently of whole-surface compactness.
Second countability then follows from the already constructed planar charts.
-/

noncomputable section

namespace MNEC.RegularCountability

open LatticeTorus CutTorus SlitConnectedSum OffSlitEmbeddings RegularPoints
open RegularChartedSpace CutTorusBoundary Set Topology

abbrev InteriorParameter := ↥(Ioo (0 : ℝ) 1)

def closedParameter (t : InteriorParameter) : Parameter :=
  ⟨t, t.property.1.le, t.property.2.le⟩

theorem continuous_closedParameter : Continuous closedParameter :=
  continuous_subtype_val.subtype_mk _

def leftRegular (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₁ w) : Regular L₁ L₂ w :=
  ⟨leftOff L₁ L₂ w p, leftOff_mem_regular L₁ L₂ w p⟩

def rightRegular (L₁ L₂ : Lattice) (w : Plane) (p : OffSlit L₂ w) : Regular L₁ L₂ w :=
  ⟨rightOff L₁ L₂ w p, rightOff_mem_regular L₁ L₂ w p⟩

def axisRegular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (k : Bool) (t : InteriorParameter) : Regular L₁ L₂ w :=
  ⟨interiorPoint L₁ L₂ w t t.property k,
    interiorPoint_mem_regular L₁ L₂ w hw₁ hw₂ t t.property k⟩

theorem continuous_leftRegular (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    Continuous (leftRegular L₁ L₂ w) :=
  (continuous_leftOff L₁ L₂ w hw).subtype_mk _

theorem continuous_rightRegular (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    Continuous (rightRegular L₁ L₂ w) :=
  (continuous_rightOff L₁ L₂ w hw).subtype_mk _

theorem continuous_interiorPoint (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (k : Bool) :
    Continuous (fun t : InteriorParameter => interiorPoint L₁ L₂ w t t.property k) := by
  have h : Continuous (fun t : InteriorParameter =>
      left L₁ L₂ w (boundaryArc L₁ w k (closedParameter t))) :=
    (continuous_left L₁ L₂ w).comp
      ((continuous_boundaryArc L₁ w hw₁ k).comp continuous_closedParameter)
  convert h using 1
  funext t
  exact congrArg (left L₁ L₂ w)
    (boundaryArc_interior L₁ w k (closedParameter t) t.property).symm

theorem continuous_axisRegular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (k : Bool) :
    Continuous (axisRegular hw₁ hw₂ k) :=
  (continuous_interiorPoint L₁ L₂ w hw₁ k).subtype_mk _

abbrev CoverSource (L₁ L₂ : Lattice) (w : Plane) :=
  OffSlit L₁ w ⊕ (OffSlit L₂ w ⊕ (InteriorParameter ⊕ InteriorParameter))

def coverMap {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    CoverSource L₁ L₂ w → Regular L₁ L₂ w :=
  Sum.elim (leftRegular L₁ L₂ w)
    (Sum.elim (rightRegular L₁ L₂ w)
      (Sum.elim (axisRegular hw₁ hw₂ false) (axisRegular hw₁ hw₂ true)))

theorem continuous_coverMap {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) : Continuous (coverMap hw₁ hw₂) :=
  (continuous_leftRegular L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁)).sumElim
    ((continuous_rightRegular L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁)).sumElim
      ((continuous_axisRegular hw₁ hw₂ false).sumElim (continuous_axisRegular hw₁ hw₂ true)))

theorem coverMap_surjective {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    Function.Surjective (coverMap hw₁ hw₂) := by
  intro p
  rcases regular_classification L₁ L₂ w hw₁ hw₂ p.val p.property with
    ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨t, ht, k, h⟩
  · exact ⟨Sum.inl q, Subtype.ext hq⟩
  · exact ⟨Sum.inr (Sum.inl q), Subtype.ext hq⟩
  · cases k
    · exact ⟨Sum.inr (Sum.inr (Sum.inl ⟨t, ht⟩)), Subtype.ext h.symm⟩
    · exact ⟨Sum.inr (Sum.inr (Sum.inr ⟨t, ht⟩)), Subtype.ext h.symm⟩

theorem sigmaCompactOffSlit (L : Lattice) (w : Plane) : SigmaCompactSpace (OffSlit L w) := by
  let : LocallyCompactSpace (OffSlit L w) := (L.slitSet_closed w).isOpen_compl.locallyCompactSpace
  infer_instance

theorem sigmaCompactInteriorParameter : SigmaCompactSpace InteriorParameter := by
  let : LocallyCompactSpace InteriorParameter :=
    (isOpen_Ioo : IsOpen (Ioo (0 : ℝ) 1)).locallyCompactSpace
  infer_instance

/-- Sigma compactness follows from a finite union of continuous images of
standard sigma compact domains, with no compactness premise on the quotient. -/
theorem sigmaCompactRegular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    SigmaCompactSpace (Regular L₁ L₂ w) := by
  let : SigmaCompactSpace (OffSlit L₁ w) := sigmaCompactOffSlit L₁ w
  let : SigmaCompactSpace (OffSlit L₂ w) := sigmaCompactOffSlit L₂ w
  let : SigmaCompactSpace InteriorParameter := sigmaCompactInteriorParameter
  have hcompact : IsSigmaCompact (range (coverMap hw₁ hw₂)) :=
    isSigmaCompact_range (continuous_coverMap hw₁ hw₂)
  have hrange : range (coverMap hw₁ hw₂) = univ :=
    Set.range_eq_univ.mpr (coverMap_surjective hw₁ hw₂)
  exact ⟨by simpa only [hrange] using hcompact⟩

/-- A countable topology is derived from sigma compactness and the actual
charted-space construction, rather than assumed as part of an atlas record. -/
theorem secondCountableRegular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    SecondCountableTopology (Regular L₁ L₂ w) := by
  let := RegularChartedSpace.chartedSpace hw₁ hw₂
  let := sigmaCompactRegular hw₁ hw₂
  exact ChartedSpace.secondCountable_of_sigmaCompact (H := Plane) (M := Regular L₁ L₂ w)

end MNEC.RegularCountability
