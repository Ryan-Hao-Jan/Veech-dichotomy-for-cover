module

public import MNEC.RegularChartedSpace
public import MNEC.SlitQuotientSeparation
public import MNEC.ConnectedSumArea

@[expose] public section

/-!
# Hausdorff topology and full physical area on the actual regular locus

The regular locus is the constructed quotient minus its two endpoint
classes. Its Hausdorffness comes from the proved quotient separation.
The endpoints lie in the proved null seam. Removing them preserves the
entire positive finite physical area, and the actual subtype inclusion
is measure preserving. No surface compactness or genus is asserted.
-/

noncomputable section

namespace MNEC.RegularTopologyArea

open LatticeTorus SlitConnectedSum OffSlitEmbeddings RegularPoints RegularAtlasCoverage
open RegularChartedSpace SlitQuotientSeparation ConnectedSumArea MeasureTheory Set Topology
open scoped ENNReal Classical

theorem regularT2Space (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    T2Space (Regular L₁ L₂ w) := by
  let _ := surfaceT2Space L₁ L₂ w hw₁ hw₂
  infer_instance

theorem endpointSet_subset_seam (L₁ L₂ : Lattice) (w : Plane) :
    endpointSet L₁ L₂ w ⊆ seam L₁ L₂ w := by
  intro p hp
  have ht : offTrace L₁ L₂ w p = none := by
    simp only [endpointSet, mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact offTrace_initialPoint L₁ L₂ w
    · exact offTrace_terminalPoint L₁ L₂ w
  change p ∉ range (leftOff L₁ L₂ w) ∪ range (rightOff L₁ L₂ w)
  rw [union_off_ranges]
  exact fun h => h ht

theorem endpointSet_area_zero (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) : area L₁ L₂ w (endpointSet L₁ L₂ w) = 0 :=
  measure_mono_null (endpointSet_subset_seam L₁ L₂ w)
    (seam_area_zero L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁))

theorem ae_mem_regularSet (L₁ L₂ : Lattice) (w : Plane) (hw₁ : L₁.EmbeddedSlit w) :
    ∀ᵐ p ∂area L₁ L₂ w, p ∈ regularSet L₁ L₂ w :=
  measure_eq_zero_iff_ae_notMem.mp (endpointSet_area_zero L₁ L₂ w hw₁)

theorem regularSet_ae_eq_univ (L₁ L₂ : Lattice) (w : Plane) (hw₁ : L₁.EmbeddedSlit w) :
    regularSet L₁ L₂ w =ᵐ[area L₁ L₂ w] univ := by
  filter_upwards [ae_mem_regularSet L₁ L₂ w hw₁] with p hp
  exact propext ⟨fun _ => Set.mem_univ _, fun _ => hp⟩

theorem regularSet_full_area (L₁ L₂ : Lattice) (w : Plane) (hw₁ : L₁.EmbeddedSlit w) :
    area L₁ L₂ w (regularSet L₁ L₂ w) = area L₁ L₂ w univ :=
  measure_congr (regularSet_ae_eq_univ L₁ L₂ w hw₁)

theorem regularSet_area (L₁ L₂ : Lattice) (w : Plane) (hw₁ : L₁.EmbeddedSlit w) :
    area L₁ L₂ w (regularSet L₁ L₂ w) = ENNReal.ofReal (L₁.covolume + L₂.covolume) := by
  rw [regularSet_full_area L₁ L₂ w hw₁,
    area_univ L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁),
    ENNReal.ofReal_add L₁.covolume_pos.le L₂.covolume_pos.le]

def regularArea (L₁ L₂ : Lattice) (w : Plane) : Measure (Regular L₁ L₂ w) :=
  (area L₁ L₂ w).comap Subtype.val

theorem regularArea_univ (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    regularArea L₁ L₂ w univ = ENNReal.ofReal (L₁.covolume + L₂.covolume) := by
  rw [regularArea, comap_subtype_coe_apply (regularSet_open hw₁ hw₂).measurableSet]
  simpa only [Set.image_univ, Subtype.range_coe] using regularSet_area L₁ L₂ w hw₁

theorem regularArea_univ_pos (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    0 < regularArea L₁ L₂ w univ := by
  rw [regularArea_univ L₁ L₂ w hw₁ hw₂]
  exact ENNReal.ofReal_pos.mpr (add_pos L₁.covolume_pos L₂.covolume_pos)

theorem regularArea_univ_ne_top (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    regularArea L₁ L₂ w univ ≠ ∞ := by
  rw [regularArea_univ L₁ L₂ w hw₁ hw₂]
  exact ENNReal.ofReal_ne_top

theorem regularArea_finite (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    IsFiniteMeasure (regularArea L₁ L₂ w) where
  measure_univ_lt_top := (regularArea_univ_ne_top L₁ L₂ w hw₁ hw₂).lt_top

/-- The independently defined measure on the actual regular subtype maps
to the full surface area, because the two omitted endpoints have zero area. -/
theorem regular_inclusion_measurePreserving (L₁ L₂ : Lattice) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    MeasurePreserving (Subtype.val : Regular L₁ L₂ w → Surface L₁ L₂ w)
      (regularArea L₁ L₂ w) (area L₁ L₂ w) where
  measurable := measurable_subtype_coe
  map_eq := by
    rw [regularArea, map_comap_subtype_coe (regularSet_open hw₁ hw₂).measurableSet,
      Measure.restrict_eq_self_of_ae_mem (ae_mem_regularSet L₁ L₂ w hw₁)]

end MNEC.RegularTopologyArea
