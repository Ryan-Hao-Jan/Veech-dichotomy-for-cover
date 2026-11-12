module

public import MNEC.SurfaceLatticeRebasing
public import MNEC.RebasedLatticeArea
public import MNEC.ConnectedSumArea
public import MNEC.RegularTopologyArea

@[expose] public section

/-!
# Actual physical area transport under primitive surface rebasing

Torus area transport restricts to the actual slit complements. The two
off-slit conjugacy identities then carry the sum of the actual piece-area
pushforwards to the original surface area. The primitive specialization
discharges torus preservation using the computed determinant-one basis.
-/

noncomputable section

namespace MNEC.SurfaceRebasingArea

open LatticeTorus SlitConnectedSum CutLatticeRebasing SurfaceLatticeRebasing
open ConnectedSumArea PrimitiveLatticeRebasing MeasureTheory Set Topology

variable {L M L₁ L₂ M₁ M₂ : Lattice}

theorem offHomeomorph_image_preimage (e : PhysicalTorusEquiv L M) (w : Plane)
    (s : Set (OffSlit L w)) :
    (Subtype.val : OffSlit M w → Torus) '' (offHomeomorph e w ⁻¹' s) =
      e.torus ⁻¹' ((Subtype.val : OffSlit L w → Torus) '' s) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨offHomeomorph e w p, hp, rfl⟩
  · rintro ⟨p, hp, hpq⟩
    refine ⟨(offHomeomorph e w).symm p, ?_, ?_⟩
    · change offHomeomorph e w ((offHomeomorph e w).symm p) ∈ s
      simpa only [Homeomorph.apply_symm_apply] using hp
    · have heq := congrArg Subtype.val ((offHomeomorph e w).apply_symm_apply p)
      change e.torus ((offHomeomorph e w).symm p).val = p.val at heq
      exact e.torus.injective (heq.trans hpq)

theorem offHomeomorph_measurePreserving (e : PhysicalTorusEquiv L M) (w : Plane)
    (hMP : MeasurePreserving e.torus M.area L.area) :
    MeasurePreserving (offHomeomorph e w) (offArea M w) (offArea L w) where
  measurable := (offHomeomorph e w).continuous.measurable
  map_eq := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (offHomeomorph e w).continuous.measurable hs,
      offArea, comap_subtype_coe_apply (M.slitSet_closed w).measurableSet.compl,
      offArea, comap_subtype_coe_apply (L.slitSet_closed w).measurableSet.compl,
      offHomeomorph_image_preimage]
    exact hMP.measure_preimage_emb e.torus.measurableEmbedding _

theorem map_surfaceHomeomorph_left_piece (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (hw : w ≠ 0)
    (hMP₁ : MeasurePreserving e₁.torus M₁.area L₁.area) :
    Measure.map (surfaceHomeomorph e₁ e₂ w)
      ((offArea M₁ w).map (leftOff M₁ M₂ w)) =
        (offArea L₁ w).map (leftOff L₁ L₂ w) := by
  rw [Measure.map_map (surfaceHomeomorph e₁ e₂ w).continuous.measurable
    (leftOff_measurableEmbedding M₁ M₂ w hw).measurable]
  have heq : surfaceHomeomorph e₁ e₂ w ∘ leftOff M₁ M₂ w =
      leftOff L₁ L₂ w ∘ offHomeomorph e₁ w := by
    funext p
    exact surfaceHomeomorph_leftOff e₁ e₂ w p
  rw [heq, ← Measure.map_map (leftOff_measurableEmbedding L₁ L₂ w hw).measurable
    (offHomeomorph e₁ w).continuous.measurable,
    (offHomeomorph_measurePreserving e₁ w hMP₁).map_eq]

theorem map_surfaceHomeomorph_right_piece (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (hw : w ≠ 0)
    (hMP₂ : MeasurePreserving e₂.torus M₂.area L₂.area) :
    Measure.map (surfaceHomeomorph e₁ e₂ w)
      ((offArea M₂ w).map (rightOff M₁ M₂ w)) =
        (offArea L₂ w).map (rightOff L₁ L₂ w) := by
  rw [Measure.map_map (surfaceHomeomorph e₁ e₂ w).continuous.measurable
    (rightOff_measurableEmbedding M₁ M₂ w hw).measurable]
  have heq : surfaceHomeomorph e₁ e₂ w ∘ rightOff M₁ M₂ w =
      rightOff L₁ L₂ w ∘ offHomeomorph e₂ w := by
    funext p
    exact surfaceHomeomorph_rightOff e₁ e₂ w p
  rw [heq, ← Measure.map_map (rightOff_measurableEmbedding L₁ L₂ w hw).measurable
    (offHomeomorph e₂ w).continuous.measurable,
    (offHomeomorph_measurePreserving e₂ w hMP₂).map_eq]

theorem surfaceHomeomorph_measurePreserving (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (hw : w ≠ 0)
    (hMP₁ : MeasurePreserving e₁.torus M₁.area L₁.area)
    (hMP₂ : MeasurePreserving e₂.torus M₂.area L₂.area) :
    MeasurePreserving (surfaceHomeomorph e₁ e₂ w) (area M₁ M₂ w) (area L₁ L₂ w) where
  measurable := (surfaceHomeomorph e₁ e₂ w).continuous.measurable
  map_eq := by
    rw [area, Measure.map_add _ _ (surfaceHomeomorph e₁ e₂ w).continuous.measurable,
      map_surfaceHomeomorph_left_piece e₁ e₂ w hw hMP₁,
      map_surfaceHomeomorph_right_piece e₁ e₂ w hw hMP₂]
    rfl

theorem map_surfaceHomeomorph_area (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (hw : w ≠ 0)
    (hMP₁ : MeasurePreserving e₁.torus M₁.area L₁.area)
    (hMP₂ : MeasurePreserving e₂.torus M₂.area L₂.area) :
    Measure.map (surfaceHomeomorph e₁ e₂ w) (area M₁ M₂ w) = area L₁ L₂ w :=
  (surfaceHomeomorph_measurePreserving e₁ e₂ w hw hMP₁ hMP₂).map_eq

theorem rebasedSurfaceHomeomorph_measurePreserving (L₁ L₂ : Lattice) (w : Plane)
    (m₁ n₁ m₂ n₂ : ℤ) (h₁ : Primitive m₁ n₁) (h₂ : Primitive m₂ n₂) (hw : w ≠ 0) :
    MeasurePreserving (rebasedSurfaceHomeomorph L₁ L₂ w m₁ n₁ m₂ n₂ h₁ h₂)
      (area (rebased L₁ m₁ n₁ h₁) (rebased L₂ m₂ n₂ h₂) w) (area L₁ L₂ w) := by
  apply surfaceHomeomorph_measurePreserving
    (PhysicalTorusEquiv.primitive L₁ m₁ n₁ h₁) (PhysicalTorusEquiv.primitive L₂ m₂ n₂ h₂) w hw
  · simpa only [PhysicalTorusEquiv.primitive] using
      RebasedLatticeArea.torusHomeomorph_measurePreserving L₁ m₁ n₁ h₁
  · simpa only [PhysicalTorusEquiv.primitive] using
      RebasedLatticeArea.torusHomeomorph_measurePreserving L₂ m₂ n₂ h₂

theorem map_rebasedSurfaceHomeomorph_area (L₁ L₂ : Lattice) (w : Plane)
    (m₁ n₁ m₂ n₂ : ℤ) (h₁ : Primitive m₁ n₁) (h₂ : Primitive m₂ n₂) (hw : w ≠ 0) :
    Measure.map (rebasedSurfaceHomeomorph L₁ L₂ w m₁ n₁ m₂ n₂ h₁ h₂)
      (area (rebased L₁ m₁ n₁ h₁) (rebased L₂ m₂ n₂ h₂) w) = area L₁ L₂ w :=
  (rebasedSurfaceHomeomorph_measurePreserving L₁ L₂ w m₁ n₁ m₂ n₂ h₁ h₂ hw).map_eq

open RegularChartedSpace RegularTopologyArea RegularAtlasCoverage

theorem regularHomeomorph_image_preimage (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (s : Set (Regular L₁ L₂ w)) :
    (Subtype.val : Regular M₁ M₂ w → Surface M₁ M₂ w) ''
        (regularHomeomorph e₁ e₂ w ⁻¹' s) =
      surfaceHomeomorph e₁ e₂ w ⁻¹'
        ((Subtype.val : Regular L₁ L₂ w → Surface L₁ L₂ w) '' s) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨regularHomeomorph e₁ e₂ w p, hp, rfl⟩
  · rintro ⟨p, hp, hpq⟩
    refine ⟨(regularHomeomorph e₁ e₂ w).symm p, ?_, ?_⟩
    · change regularHomeomorph e₁ e₂ w ((regularHomeomorph e₁ e₂ w).symm p) ∈ s
      simpa only [Homeomorph.apply_symm_apply] using hp
    · have heq := congrArg Subtype.val ((regularHomeomorph e₁ e₂ w).apply_symm_apply p)
      change surfaceHomeomorph e₁ e₂ w ((regularHomeomorph e₁ e₂ w).symm p).val = p.val at heq
      exact (surfaceHomeomorph e₁ e₂ w).injective (heq.trans hpq)

theorem regularHomeomorph_measurePreserving (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (hMP₁ : MeasurePreserving e₁.torus M₁.area L₁.area)
    (hMP₂ : MeasurePreserving e₂.torus M₂.area L₂.area) :
    MeasurePreserving (regularHomeomorph e₁ e₂ w)
      (regularArea M₁ M₂ w) (regularArea L₁ L₂ w) := by
  have hM₁ : M₁.EmbeddedSlit w := by
    intro s t hst
    apply hw₁
    simpa only [e₁.arc_eq] using congrArg e₁.torus hst
  have hM₂ : M₂.EmbeddedSlit w := by
    intro s t hst
    apply hw₂
    simpa only [e₂.arc_eq] using congrArg e₂.torus hst
  have hSurface := surfaceHomeomorph_measurePreserving e₁ e₂ w
    (OffSlitEmbeddings.embeddedSlit_ne_zero L₁ w hw₁) hMP₁ hMP₂
  refine ⟨(regularHomeomorph e₁ e₂ w).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (regularHomeomorph e₁ e₂ w).continuous.measurable hs,
    regularArea, comap_subtype_coe_apply (regularSet_open hM₁ hM₂).measurableSet,
    regularArea, comap_subtype_coe_apply (regularSet_open hw₁ hw₂).measurableSet,
    regularHomeomorph_image_preimage]
  exact hSurface.measure_preimage_emb (surfaceHomeomorph e₁ e₂ w).measurableEmbedding _

theorem rebasedRegularHomeomorph_measurePreserving (L₁ L₂ : Lattice) (w : Plane)
    (m₁ n₁ m₂ n₂ : ℤ) (h₁ : Primitive m₁ n₁) (h₂ : Primitive m₂ n₂)
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w) :
    MeasurePreserving
      (regularHomeomorph (PhysicalTorusEquiv.primitive L₁ m₁ n₁ h₁)
        (PhysicalTorusEquiv.primitive L₂ m₂ n₂ h₂) w)
      (regularArea (rebased L₁ m₁ n₁ h₁) (rebased L₂ m₂ n₂ h₂) w)
      (regularArea L₁ L₂ w) := by
  apply regularHomeomorph_measurePreserving
    (PhysicalTorusEquiv.primitive L₁ m₁ n₁ h₁) (PhysicalTorusEquiv.primitive L₂ m₂ n₂ h₂) w hw₁ hw₂
  · simpa only [PhysicalTorusEquiv.primitive] using
      RebasedLatticeArea.torusHomeomorph_measurePreserving L₁ m₁ n₁ h₁
  · simpa only [PhysicalTorusEquiv.primitive] using
      RebasedLatticeArea.torusHomeomorph_measurePreserving L₂ m₂ n₂ h₂

end MNEC.SurfaceRebasingArea

