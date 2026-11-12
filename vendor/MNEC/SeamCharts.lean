module

public import MNEC.SeamChartAxis
public import MNEC.SeamChartOffAxis
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section

/-!
# Constructed open partial homeomorphisms across a general slit seam

The rectangle maps are continuous, injective and open by independent
proofs on the axis and off it. The physical charts use the actual signed
plane frame, so their planar coordinates are physical flat coordinates.
Translation transitions and endpoint cone charts are separate results.
-/

noncomputable section

namespace MNEC.SeamCharts

open LatticeTorus CutTorus SlitConnectedSum OffSlitEmbeddings SlitCollars CutBankLifts
open SeamChartMaps SeamChartRange SeamChartAxis SeamChartOffAxis Set Topology

theorem isOpenMap_chart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : IsOpenMap (chart C k) := by
  intro V hV
  apply isOpen_iff_forall_mem_open.mpr
  rintro p ⟨q, hq, rfl⟩
  by_cases hz : q.val.2 = 0
  · obtain ⟨O, hO, hmem, hsub⟩ :=
      exists_open_image_neighborhood_of_zero hw₁ hw₂ C k V hV q hq hz
    exact ⟨O, hsub, hO, hmem⟩
  · obtain ⟨O, hO, hmem, hsub⟩ :=
      exists_open_image_neighborhood_of_ne_zero hw₁ hw₂ C k V hV q hq hz
    exact ⟨O, hsub, hO, hmem⟩

theorem isOpenEmbedding_chart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : IsOpenEmbedding (chart C k) :=
  .of_continuous_injective_isOpenMap (continuous_chart hw₁ hw₂ C k)
    (chart_injective hw₁ hw₂ C k) (isOpenMap_chart hw₁ hw₂ C k)

abbrev rectangleOpen {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w) :
    TopologicalSpace.Opens Plane := ⟨rectangle C.a C.b C.r, isOpen_Ioo.prod isOpen_Ioo⟩

theorem domain_nonempty {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w) :
    Nonempty (Domain C) := by
  refine ⟨⟨((C.a + C.b) / 2, 0), ?_⟩⟩
  exact ⟨⟨by linarith only [C.a_lt_b], by linarith only [C.a_lt_b]⟩,
    ⟨neg_lt_zero.mpr C.r_pos, C.r_pos⟩⟩

def coordinateChart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : OpenPartialHomeomorph Plane (Surface L₁ L₂ w) :=
  (((rectangleOpen C).openPartialHomeomorphSubtypeCoe (domain_nonempty C)).lift_openEmbedding
    (isOpenEmbedding_chart hw₁ hw₂ C k)).symm

theorem coordinateChart_source {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    (coordinateChart hw₁ hw₂ C k).source = rectangle C.a C.b C.r := by
  unfold coordinateChart
  rw [OpenPartialHomeomorph.lift_openEmbedding_symm_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  rfl

theorem coordinateChart_target {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    (coordinateChart hw₁ hw₂ C k).target = SeamOpenSets.seamNeighborhood C k := by
  unfold coordinateChart
  rw [OpenPartialHomeomorph.lift_openEmbedding_symm_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source, Set.image_univ,
    range_chart]

theorem coordinateChart_apply {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (p : Plane)
    (hp : p ∈ rectangle C.a C.b C.r) :
    coordinateChart hw₁ hw₂ C k p = chart C k ⟨p, hp⟩ := by
  let e := (rectangleOpen C).openPartialHomeomorphSubtypeCoe (domain_nonempty C)
  change chart C k (e.symm p) = chart C k ⟨p, hp⟩
  congr 1
  apply Subtype.ext
  apply e.right_inv
  change p ∈ ((rectangleOpen C).openPartialHomeomorphSubtypeCoe (domain_nonempty C)).target
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  exact hp

def physicalChart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : OpenPartialHomeomorph Plane (Surface L₁ L₂ w) :=
  (signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k).symm.transOpenPartialHomeomorph
    (coordinateChart hw₁ hw₂ C k)

theorem physicalChart_source {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    (physicalChart hw₁ hw₂ C k).source =
      (signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k).symm ⁻¹'
        rectangle C.a C.b C.r := by
  change (signedFrameHomeomorph w (embeddedSlit_ne_zero L₁ w hw₁) k).symm ⁻¹'
    (coordinateChart hw₁ hw₂ C k).source = _
  rw [coordinateChart_source]

theorem physicalChart_target {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    (physicalChart hw₁ hw₂ C k).target = SeamOpenSets.seamNeighborhood C k :=
  coordinateChart_target hw₁ hw₂ C k

theorem axis_mem_target {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) (t : ℝ) (ht : t ∈ Ioo C.a C.b) :
    left L₁ L₂ w (interiorBank L₁ w k t
      ⟨C.a_pos.trans ht.1, ht.2.trans C.b_lt_one⟩) ∈ (physicalChart hw₁ hw₂ C k).target := by
  let q : Domain C := ⟨(t, 0), ⟨ht, ⟨neg_lt_zero.mpr C.r_pos, C.r_pos⟩⟩⟩
  rw [physicalChart_target, ← range_chart]
  refine ⟨q, ?_⟩
  rw [chart_zero C k q rfl]
  unfold positiveExtension
  rw [halfLift_zero C.leftCollar k (leftAbsHalf C q) (by change |(0 : ℝ)| = 0; exact abs_zero)]
  rfl

end MNEC.SeamCharts
