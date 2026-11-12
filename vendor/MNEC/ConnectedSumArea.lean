module

public import MNEC.LatticeTorusMeasure
public import MNEC.OffSlitEmbeddings
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

/-!
# Area on the physical two-lattice slit quotient

The measure is constructed on the actual topological quotient: push forward
the two independent lattice-torus areas off their null slits, then add them.
The two open pieces have precisely their respective covolumes, the total
is their sum, and the remaining seam is null. No flow, genus assertion, or
flat-chart identification across the seam is assumed or proved here.
-/

noncomputable section

namespace MNEC.ConnectedSumArea

open LatticeTorus SlitConnectedSum OffSlitEmbeddings MeasureTheory Set Topology
open scoped ENNReal Classical

instance surfaceMeasurableSpace (L₁ L₂ : Lattice) (w : Plane) :
    MeasurableSpace (Surface L₁ L₂ w) := borel _

instance surfaceBorelSpace (L₁ L₂ : Lattice) (w : Plane) :
    BorelSpace (Surface L₁ L₂ w) := ⟨rfl⟩

def offArea (L : Lattice) (w : Plane) : Measure (OffSlit L w) :=
  L.area.comap Subtype.val

theorem offArea_univ (L : Lattice) (w : Plane) :
    offArea L w univ = ENNReal.ofReal L.covolume := by
  rw [offArea, comap_subtype_coe_apply (L.slitSet_closed w).measurableSet.compl]
  simpa only [Set.image_univ, Subtype.range_coe] using L.area_off_slit w

theorem leftOff_measurableEmbedding (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    MeasurableEmbedding (leftOff L₁ L₂ w) :=
  (isOpenEmbedding_leftOff L₁ L₂ w hw).measurableEmbedding

theorem rightOff_measurableEmbedding (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    MeasurableEmbedding (rightOff L₁ L₂ w) :=
  (isOpenEmbedding_rightOff L₁ L₂ w hw).measurableEmbedding

def area (L₁ L₂ : Lattice) (w : Plane) : Measure (Surface L₁ L₂ w) :=
  (offArea L₁ w).map (leftOff L₁ L₂ w) + (offArea L₂ w).map (rightOff L₁ L₂ w)

theorem area_univ (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    area L₁ L₂ w univ = ENNReal.ofReal L₁.covolume + ENNReal.ofReal L₂.covolume := by
  rw [area, Measure.add_apply,
    (leftOff_measurableEmbedding L₁ L₂ w hw).map_apply,
    (rightOff_measurableEmbedding L₁ L₂ w hw).map_apply]
  simp only [preimage_univ, offArea_univ]

theorem area_univ_pos (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    0 < area L₁ L₂ w univ := by
  rw [area_univ L₁ L₂ w hw]
  exact (ENNReal.ofReal_pos.mpr L₁.covolume_pos).trans_le (le_add_right le_rfl)

theorem area_univ_ne_top (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    area L₁ L₂ w univ ≠ ∞ := by
  rw [area_univ L₁ L₂ w hw]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩

theorem left_range_open (L₁ L₂ : Lattice) (w : Plane) :
    IsOpen (range (leftOff L₁ L₂ w)) := (isOpenMap_leftOff L₁ L₂ w).isOpen_range

theorem right_range_open (L₁ L₂ : Lattice) (w : Plane) :
    IsOpen (range (rightOff L₁ L₂ w)) := (isOpenMap_rightOff L₁ L₂ w).isOpen_range

theorem rightOff_preimage_left_range (L₁ L₂ : Lattice) (w : Plane) :
    (rightOff L₁ L₂ w) ⁻¹' range (leftOff L₁ L₂ w) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact Set.disjoint_left.mp (off_images_disjoint L₁ L₂ w) hp ⟨p, rfl⟩

theorem leftOff_preimage_right_range (L₁ L₂ : Lattice) (w : Plane) :
    (leftOff L₁ L₂ w) ⁻¹' range (rightOff L₁ L₂ w) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact Set.disjoint_left.mp (off_images_disjoint L₁ L₂ w) ⟨p, rfl⟩ hp

theorem area_left_range (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    area L₁ L₂ w (range (leftOff L₁ L₂ w)) = ENNReal.ofReal L₁.covolume := by
  rw [area, Measure.add_apply,
    (leftOff_measurableEmbedding L₁ L₂ w hw).map_apply,
    (rightOff_measurableEmbedding L₁ L₂ w hw).map_apply,
    rightOff_preimage_left_range]
  have hl : (leftOff L₁ L₂ w) ⁻¹' range (leftOff L₁ L₂ w) = univ := by
    ext p
    simp
  simp only [hl, measure_empty, add_zero, offArea_univ]

theorem area_right_range (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    area L₁ L₂ w (range (rightOff L₁ L₂ w)) = ENNReal.ofReal L₂.covolume := by
  rw [area, Measure.add_apply,
    (leftOff_measurableEmbedding L₁ L₂ w hw).map_apply,
    (rightOff_measurableEmbedding L₁ L₂ w hw).map_apply,
    leftOff_preimage_right_range]
  have hr : (rightOff L₁ L₂ w) ⁻¹' range (rightOff L₁ L₂ w) = univ := by
    ext p
    simp
  simp only [hr, measure_empty, zero_add, offArea_univ]

def seam (L₁ L₂ : Lattice) (w : Plane) : Set (Surface L₁ L₂ w) :=
  (range (leftOff L₁ L₂ w) ∪ range (rightOff L₁ L₂ w))ᶜ

theorem seam_closed (L₁ L₂ : Lattice) (w : Plane) : IsClosed (seam L₁ L₂ w) :=
  ((left_range_open L₁ L₂ w).union (right_range_open L₁ L₂ w)).isClosed_compl

theorem seam_area_zero (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    area L₁ L₂ w (seam L₁ L₂ w) = 0 := by
  rw [area, Measure.add_apply,
    (leftOff_measurableEmbedding L₁ L₂ w hw).map_apply,
    (rightOff_measurableEmbedding L₁ L₂ w hw).map_apply]
  have hl : (leftOff L₁ L₂ w) ⁻¹' seam L₁ L₂ w = ∅ := by
    ext p
    simp [seam]
  have hr : (rightOff L₁ L₂ w) ⁻¹' seam L₁ L₂ w = ∅ := by
    ext p
    simp [seam]
  simp [hl, hr]

end MNEC.ConnectedSumArea
