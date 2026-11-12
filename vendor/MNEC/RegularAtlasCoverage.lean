module

public import MNEC.RegularPoints
public import MNEC.OffSlitCharts
public import MNEC.SeamCharts

@[expose] public section

/-!
# Constructed physical charts cover precisely the regular locus

The indexed family consists of the actual off-slit and seam physical open
partial homeomorphisms. Their targets avoid both endpoint classes and cover
every other quotient point. Openness of the regular locus and closedness of
the endpoint set follow from this proved cover, with no separation axiom.
Translation transitions and endpoint cone charts are separate obligations.
-/

noncomputable section

namespace MNEC.RegularAtlasCoverage

open LatticeTorus CutTorus SlitConnectedSum SlitCollars OffSlitEmbeddings
open RegularPoints SeamOpenSets Set Topology

inductive Index (L₁ L₂ : Lattice) (w : Plane) where
  | left (a : Plane)
  | right (a : Plane)
  | seam (C : CommonCollar L₁ L₂ w) (k : Bool)

/-- An indexed family of independently constructed physical planar charts. -/
def chart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    Index L₁ L₂ w → OpenPartialHomeomorph Plane (Surface L₁ L₂ w)
  | .left a => OffSlitCharts.leftChart L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a
  | .right a => OffSlitCharts.rightChart L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a
  | .seam C k => SeamCharts.physicalChart hw₁ hw₂ C k

theorem leftChart_target_subset_regular (L₁ L₂ : Lattice) (w : Plane)
    (hw : w ≠ 0) (a : Plane) :
    (OffSlitCharts.leftChart L₁ L₂ w hw a).target ⊆ regularSet L₁ L₂ w := by
  intro p hp
  change p ∈ leftOff L₁ L₂ w '' (OffSlitCharts.offTorusChart L₁ w a).source at hp
  obtain ⟨q, _, rfl⟩ := hp
  exact leftOff_mem_regular L₁ L₂ w q

theorem rightChart_target_subset_regular (L₁ L₂ : Lattice) (w : Plane)
    (hw : w ≠ 0) (a : Plane) :
    (OffSlitCharts.rightChart L₁ L₂ w hw a).target ⊆ regularSet L₁ L₂ w := by
  intro p hp
  change p ∈ rightOff L₁ L₂ w '' (OffSlitCharts.offTorusChart L₂ w a).source at hp
  obtain ⟨q, _, rfl⟩ := hp
  exact rightOff_mem_regular L₁ L₂ w q

theorem initial_not_mem_seamNeighborhood {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    initialPoint L₁ L₂ w ∉ seamNeighborhood C k := by
  intro h
  have hpre : Sum.inl (upper L₁ w (L₁.project 0)) ∈
      glue L₁ L₂ w ⁻¹' (glue L₁ L₂ w '' rawNeighborhood C k) := h
  rw [preimage_image_rawNeighborhood hw₁ hw₂ C k, mem_rawNeighborhood_inl] at hpre
  exact endpoint_not_mem_bankNeighborhood L₁ w hw₁ C.a C.b C.r k
    C.a_pos C.b_lt_one _ (Or.inl rfl) hpre

theorem terminal_not_mem_seamNeighborhood {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    terminalPoint L₁ L₂ w ∉ seamNeighborhood C k := by
  intro h
  have hpre : Sum.inl (upper L₁ w (L₁.project w)) ∈
      glue L₁ L₂ w ⁻¹' (glue L₁ L₂ w '' rawNeighborhood C k) := h
  rw [preimage_image_rawNeighborhood hw₁ hw₂ C k, mem_rawNeighborhood_inl] at hpre
  exact endpoint_not_mem_bankNeighborhood L₁ w hw₁ C.a C.b C.r k
    C.a_pos C.b_lt_one _ (Or.inr (Set.mem_singleton _)) hpre

theorem seamChart_target_subset_regular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    (SeamCharts.physicalChart hw₁ hw₂ C k).target ⊆ regularSet L₁ L₂ w := by
  intro p hp
  rw [SeamCharts.physicalChart_target] at hp
  rintro (h | h)
  · exact initial_not_mem_seamNeighborhood hw₁ hw₂ C k (h ▸ hp)
  · exact terminal_not_mem_seamNeighborhood hw₁ hw₂ C k
      ((Set.mem_singleton_iff.mp h) ▸ hp)

theorem chart_target_subset_regular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) (i : Index L₁ L₂ w) :
    (chart hw₁ hw₂ i).target ⊆ regularSet L₁ L₂ w := by
  cases i with
  | left a => exact leftChart_target_subset_regular L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a
  | right a => exact rightChart_target_subset_regular L₁ L₂ w (embeddedSlit_ne_zero L₁ w hw₁) a
  | seam C k => exact seamChart_target_subset_regular hw₁ hw₂ C k

/-- Every regular quotient point belongs to one target of the actual
physical chart family. -/
theorem chart_cover_regular {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (p : Surface L₁ L₂ w) (hp : p ∈ regularSet L₁ L₂ w) :
    ∃ i : Index L₁ L₂ w, p ∈ (chart hw₁ hw₂ i).target := by
  rcases regular_classification L₁ L₂ w hw₁ hw₂ p hp with
    ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨t, ht, k, rfl⟩
  · obtain ⟨a, ha⟩ := OffSlitCharts.leftChart_cover L₁ L₂ w
      (embeddedSlit_ne_zero L₁ w hw₁) q
    exact ⟨.left a, ha⟩
  · obtain ⟨a, ha⟩ := OffSlitCharts.rightChart_cover L₁ L₂ w
      (embeddedSlit_ne_zero L₁ w hw₁) q
    exact ⟨.right a, ha⟩
  · obtain ⟨C, htC⟩ := exists_common_collar_at L₁ L₂ w hw₁ hw₂ t ht
    refine ⟨.seam C k, ?_⟩
    exact SeamCharts.axis_mem_target hw₁ hw₂ C k t htC

theorem regularSet_eq_iUnion_targets {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    regularSet L₁ L₂ w = ⋃ i : Index L₁ L₂ w, (chart hw₁ hw₂ i).target := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := chart_cover_regular hw₁ hw₂ p hp
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact chart_target_subset_regular hw₁ hw₂ i hi

/-- Openness follows from the proved chart cover, without T1 or T2. -/
theorem regularSet_open {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    IsOpen (regularSet L₁ L₂ w) := by
  rw [regularSet_eq_iUnion_targets hw₁ hw₂]
  exact isOpen_iUnion fun i => (chart hw₁ hw₂ i).open_target

/-- The pair of endpoint classes is closed as a consequence of the
constructed regular charts, rather than of an assumed separation axiom. -/
theorem endpointSet_closed {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    IsClosed (endpointSet L₁ L₂ w) := by
  simpa only [regularSet, compl_compl] using
    (regularSet_open hw₁ hw₂).isClosed_compl

end MNEC.RegularAtlasCoverage
