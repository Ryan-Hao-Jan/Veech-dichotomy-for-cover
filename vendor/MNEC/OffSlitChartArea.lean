module

public import MNEC.OffSlitCharts
public import MNEC.ConnectedSumArea
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

/-!
# Proved Lebesgue area in the actual off-slit planar charts

General translated fundamental cells are treated by the actual quotient
maps and determinant change of variables. The two open embeddings preserve
the appropriate restricted measures. Finally each measurable subset of a
physical off-slit chart has quotient area equal to its planar Lebesgue area.
These are derived equalities, not assumptions identifying an intrinsic area.
-/

noncomputable section

namespace MNEC.OffSlitChartArea

open LatticeTorus SlitConnectedSum SlitCollars OffSlitCharts ConnectedSumArea
open MeasureTheory Set Topology Function
open scoped ENNReal Classical

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

local instance : (volume : Measure Plane).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  exact Measure.prod.instIsAddHaarMeasure _ _

def coordinateCell (a : Plane) : Set Plane :=
  Ioc a.1 (a.1 + 1) ×ˢ Ioc a.2 (a.2 + 1)

def physicalCell (L : Lattice) (a : Plane) : Set Plane := L.frame '' coordinateCell a

theorem standardProjection_cell_preserving (a : Plane) :
    MeasurePreserving standardProjection (volume.restrict (coordinateCell a)) canonicalArea := by
  have hm := (AddCircle.measurePreserving_mk (1 : ℝ) a.1).prod
    (AddCircle.measurePreserving_mk (1 : ℝ) a.2)
  rw [Measure.prod_restrict] at hm
  convert hm using 1 <;> rfl

theorem project_preimage_cell (L : Lattice) (a : Plane) (U : Set Torus) :
    L.project ⁻¹' U ∩ physicalCell L a =
      L.frame '' (standardProjection ⁻¹' U ∩ coordinateCell a) := by
  ext p
  constructor
  · rintro ⟨hp, x, hx, rfl⟩
    refine ⟨x, ⟨?_, hx⟩, rfl⟩
    simpa only [Set.mem_preimage, Lattice.project, standardProjection,
      ContinuousLinearEquiv.symm_apply_apply] using hp
  · rintro ⟨x, ⟨hx, hcell⟩, rfl⟩
    refine ⟨?_, x, hcell, rfl⟩
    simpa only [Set.mem_preimage, Lattice.project, standardProjection,
      ContinuousLinearEquiv.symm_apply_apply] using hx

theorem physical_projection_area (L : Lattice) (a : Plane) (U : Set Torus)
    (hU : MeasurableSet U) :
    volume (L.project ⁻¹' U ∩ physicalCell L a) = L.area U := by
  rw [project_preimage_cell,
    (volume : Measure Plane).addHaar_image_continuousLinearEquiv L.frame]
  have hstandard := (standardProjection_cell_preserving a).measure_preimage
    hU.nullMeasurableSet
  rw [Measure.restrict_apply (hU.preimage continuous_standardProjection.measurable)]
    at hstandard
  rw [hstandard]
  rfl

theorem project_injective_cell (L : Lattice) (a : Plane) : InjOn L.project (physicalCell L a) := by
  rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩ hxy
  have hcoords : standardProjection x = standardProjection y := by
    simpa only [Lattice.project, standardProjection,
      ContinuousLinearEquiv.symm_apply_apply] using hxy
  have heq : x = y := Prod.ext
    ((AddCircle.coe_eq_coe_iff_of_mem_Ioc hx.1 hy.1).mp (congrArg Prod.fst hcoords))
    ((AddCircle.coe_eq_coe_iff_of_mem_Ioc hx.2 hy.2).mp (congrArg Prod.snd hcoords))
  exact congrArg L.frame heq

theorem torusChart_source_subset_cell (L : Lattice) (a : Plane) :
    (torusChart L a).source ⊆ physicalCell L a := by
  intro p hp
  rw [torusChart_source] at hp
  exact ⟨L.frame.symm p, ⟨⟨hp.1.1, hp.1.2.le⟩, ⟨hp.2.1, hp.2.2.le⟩⟩,
    L.frame.apply_symm_apply p⟩

theorem chart_image_measurable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    (e : OpenPartialHomeomorph A B) (V : Set A) (hV : MeasurableSet V)
    (hsub : V ⊆ e.source) : MeasurableSet (e '' V) := by
  have himage : e '' V = (e.source.domRestrict e) '' (Subtype.val ⁻¹' V) := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [himage]
  exact e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image.mpr
    (hV.preimage measurable_subtype_coe)

theorem torusChart_area_image (L : Lattice) (a : Plane) (V : Set Plane)
    (hV : MeasurableSet V) (hsub : V ⊆ (torusChart L a).source) :
    L.area (L.project '' V) = volume V := by
  have hsubcell : V ⊆ physicalCell L a := hsub.trans (torusChart_source_subset_cell L a)
  have hmeas : MeasurableSet (L.project '' V) := chart_image_measurable
    (torusChart L a) V hV hsub
  have hpre : L.project ⁻¹' (L.project '' V) ∩ physicalCell L a = V := by
    ext p
    constructor
    · rintro ⟨⟨q, hq, hqp⟩, hp⟩
      have heq := project_injective_cell L a hp (hsubcell hq) hqp.symm
      exact heq ▸ hq
    · intro hp
      exact ⟨⟨p, hp, rfl⟩, hsubcell hp⟩
  rw [← physical_projection_area L a _ hmeas, hpre]

section DisjointMeasures

variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]

theorem left_image_mass (μ : Measure A) (ν : Measure B) (f : A → Z) (g : B → Z)
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (hdisj : Disjoint (range f) (range g)) (S : Set A) :
    (μ.map f + ν.map g) (f '' S) = μ S := by
  rw [Measure.add_apply, hf.map_apply, hg.map_apply, preimage_image_eq S hf.injective]
  have hpre : g ⁻¹' (f '' S) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨a, ha, hab⟩ := hb
    exact Set.disjoint_left.mp hdisj ⟨a, hab⟩ ⟨b, rfl⟩
  simp [hpre]

theorem restrict_left_measure (μ : Measure A) (ν : Measure B) (f : A → Z) (g : B → Z)
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (hdisj : Disjoint (range f) (range g)) :
    (μ.map f + ν.map g).restrict (range f) = μ.map f := by
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.add_apply, hf.map_apply, hg.map_apply, hf.map_apply]
  have hpre : f ⁻¹' (S ∩ range f) = f ⁻¹' S := by ext x; simp
  have hgpre : g ⁻¹' (S ∩ range f) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact Set.disjoint_left.mp hdisj hb.2 ⟨b, rfl⟩
  simp [hpre, hgpre]

end DisjointMeasures

theorem area_image_leftOff (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0)
    (S : Set (OffSlit L₁ w)) :
    area L₁ L₂ w (leftOff L₁ L₂ w '' S) = offArea L₁ w S :=
  left_image_mass _ _ _ _ (leftOff_measurableEmbedding L₁ L₂ w hw)
    (rightOff_measurableEmbedding L₁ L₂ w hw) (off_images_disjoint L₁ L₂ w) S

theorem area_image_rightOff (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0)
    (S : Set (OffSlit L₂ w)) :
    area L₁ L₂ w (rightOff L₁ L₂ w '' S) = offArea L₂ w S := by
  rw [area, add_comm]
  exact left_image_mass _ _ _ _ (rightOff_measurableEmbedding L₁ L₂ w hw)
    (leftOff_measurableEmbedding L₁ L₂ w hw) (off_images_disjoint L₁ L₂ w).symm S

theorem area_restrict_left_range (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    (area L₁ L₂ w).restrict (range (leftOff L₁ L₂ w)) =
      (offArea L₁ w).map (leftOff L₁ L₂ w) :=
  restrict_left_measure _ _ _ _ (leftOff_measurableEmbedding L₁ L₂ w hw)
    (rightOff_measurableEmbedding L₁ L₂ w hw) (off_images_disjoint L₁ L₂ w)

theorem area_restrict_right_range (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    (area L₁ L₂ w).restrict (range (rightOff L₁ L₂ w)) =
      (offArea L₂ w).map (rightOff L₁ L₂ w) := by
  rw [area, add_comm]
  exact restrict_left_measure _ _ _ _ (rightOff_measurableEmbedding L₁ L₂ w hw)
    (leftOff_measurableEmbedding L₁ L₂ w hw) (off_images_disjoint L₁ L₂ w).symm

theorem leftOff_measurePreserving (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    MeasurePreserving (leftOff L₁ L₂ w) (offArea L₁ w)
      ((area L₁ L₂ w).restrict (range (leftOff L₁ L₂ w))) :=
  ⟨(leftOff_measurableEmbedding L₁ L₂ w hw).measurable,
    (area_restrict_left_range L₁ L₂ w hw).symm⟩

theorem rightOff_measurePreserving (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    MeasurePreserving (rightOff L₁ L₂ w) (offArea L₂ w)
      ((area L₁ L₂ w).restrict (range (rightOff L₁ L₂ w))) :=
  ⟨(rightOff_measurableEmbedding L₁ L₂ w hw).measurable,
    (area_restrict_right_range L₁ L₂ w hw).symm⟩

theorem leftOff_comap_restricted_area (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    ((area L₁ L₂ w).restrict (range (leftOff L₁ L₂ w))).comap (leftOff L₁ L₂ w) =
      offArea L₁ w := by
  rw [area_restrict_left_range L₁ L₂ w hw]
  exact (leftOff_measurableEmbedding L₁ L₂ w hw).comap_map _

theorem rightOff_comap_restricted_area (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) :
    ((area L₁ L₂ w).restrict (range (rightOff L₁ L₂ w))).comap (rightOff L₁ L₂ w) =
      offArea L₂ w := by
  rw [area_restrict_right_range L₁ L₂ w hw]
  exact (rightOff_measurableEmbedding L₁ L₂ w hw).comap_map _

theorem offTorusChart_symm_area_image (L : Lattice) (w a : Plane) (V : Set Plane)
    (hV : MeasurableSet V) (hsub : V ⊆ (offTorusChart L w a).target) :
    offArea L w ((offTorusChart L w a).symm '' V) = volume V := by
  rw [offArea, comap_subtype_coe_apply (L.slitSet_closed w).measurableSet.compl,
    Set.image_image]
  have himage : (Subtype.val ∘ (offTorusChart L w a).symm) '' V = L.project '' V := by
    apply Set.image_congr
    intro p hp
    exact offTorusChart_symm_val L w a p (hsub hp)
  change L.area ((Subtype.val ∘ (offTorusChart L w a).symm) '' V) = volume V
  rw [himage]
  apply torusChart_area_image L a V hV
  intro p hp
  exact ((offTorusChart_target L w a) ▸ hsub hp).1

/-- Every measurable physical subset of the actual left chart has exactly
its planar Lebesgue area in the quotient. -/
theorem leftChart_area_image (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0)
    (a : Plane) (V : Set Plane) (hV : MeasurableSet V)
    (hsub : V ⊆ (leftChart L₁ L₂ w hw a).source) :
    area L₁ L₂ w ((leftChart L₁ L₂ w hw a) '' V) = volume V := by
  change area L₁ L₂ w ((fun p => leftOff L₁ L₂ w ((offTorusChart L₁ w a).symm p)) '' V) = _
  rw [← Set.image_image (leftOff L₁ L₂ w) (offTorusChart L₁ w a).symm V,
    area_image_leftOff L₁ L₂ w hw]
  exact offTorusChart_symm_area_image L₁ w a V hV hsub

/-- The same equality holds for the unrelated lattice of the right chart. -/
theorem rightChart_area_image (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0)
    (a : Plane) (V : Set Plane) (hV : MeasurableSet V)
    (hsub : V ⊆ (rightChart L₁ L₂ w hw a).source) :
    area L₁ L₂ w ((rightChart L₁ L₂ w hw a) '' V) = volume V := by
  change area L₁ L₂ w ((fun p => rightOff L₁ L₂ w ((offTorusChart L₂ w a).symm p)) '' V) = _
  rw [← Set.image_image (rightOff L₁ L₂ w) (offTorusChart L₂ w a).symm V,
    area_image_rightOff L₁ L₂ w hw]
  exact offTorusChart_symm_area_image L₂ w a V hV hsub

end MNEC.OffSlitChartArea
