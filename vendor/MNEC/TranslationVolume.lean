module

public import MNEC.TranslationGroupoid
public import MNEC.LocalAreaGluing
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Actual local translations preserve Euclidean physical volume. An open
partial homeomorphism with proved local translation germs is partitioned
by a countable subordinate Borel cover; injectivity and countable additivity
then derive its full source image-volume identity. No MP oracle is input. -/

@[expose] public section
noncomputable section
namespace MNEC.TranslationVolume

open LatticeTorus TranslationGroupoid MeasureTheory Set Topology Filter
open scoped Classical

theorem volume_translation (a : Plane) (A : Set Plane) :
    volume ((fun p : Plane => p + a) '' A) = volume A := by
  let : Measure.IsAddRightInvariant (volume : Measure Plane) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let H := Homeomorph.addRight a
  have h := (measurePreserving_add_right (volume : Measure Plane) a).measure_preimage_emb
    H.toMeasurableEquiv.measurableEmbedding ((fun p : Plane => p + a) '' A)
  have hpre : (fun p : Plane => p + a) ⁻¹' ((fun p : Plane => p + a) '' A) = A :=
    preimage_image_eq A H.injective
  rw [hpre] at h
  exact h.symm

theorem image_volume (F : OpenPartialHomeomorph Plane Plane)
    (htrans : LocallyTranslationOn F F.source) (A : Set Plane)
    (hA : MeasurableSet A) (hsub : A ⊆ F.source) : volume (F '' A) = volume A := by
  let a : F.source → Plane := fun p => (htrans p.val p.property).choose
  have ha (p : F.source) : ∀ᶠ y in 𝓝 p.val, F y = y + a p := (htrans p.val p.property).choose_spec
  let U : F.source → Set Plane := fun p => F.source ∩ interior {y | F y = y + a p}
  let E : F.source → OpenPartialHomeomorph Plane Plane := fun p => (Homeomorph.addRight (a p)).toOpenPartialHomeomorph
  have hU : ∀ p, IsOpen (U p) := fun p => F.open_source.inter isOpen_interior
  have hcover : F.source ⊆ ⋃ p, U p := by
    intro p hp
    apply mem_iUnion.mpr
    refine ⟨⟨p, hp⟩, hp, ?_⟩
    exact mem_interior_iff_mem_nhds.mpr (ha ⟨p, hp⟩)
  apply LocalAreaGluing.image_area_of_open_cover volume F U E hU hcover
  · intro p y hy
    exact mem_univ y
  · intro p y hy
    have heq : y ∈ {z : Plane | F z = z + a p} := interior_subset hy.2
    exact heq
  · intro p B _ _
    exact volume_translation (a p) B
  · exact hA
  · exact hsub

theorem image_volume_of_mem_groupoid (F : OpenPartialHomeomorph Plane Plane)
    (hF : F ∈ TranslationGroupoid.groupoid) (A : Set Plane) (hA : MeasurableSet A) (hsub : A ⊆ F.source) :
    volume (F '' A) = volume A :=
  image_volume F ((mem_groupoid_iff F).mp hF).1 A hA hsub

end MNEC.TranslationVolume
