module

public import MNEC.NativeCompleteDirectionalFlow
public import MNEC.NativePartialDirectionalArea
public import Mathlib.MeasureTheory.Group.Action

/-! Canonical physical area on the actual complete directional phase of ANY native form.
Every time map preserves this area by the proved native partial-flow area
identity. No full-area or probability hypothesis is needed here. The normalization denominator is actual regular total area; full mass and probability remain separate obligations. -/

@[expose] public section
noncomputable section

namespace MNEC.NativeCompleteDirectionalArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeCompleteDirectionalFlow
open NativeRegularArea MeasureTheory Set
open scoped ENNReal Classical Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : NativeAbelianDifferential.Differential X)
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩
local notation "R" => Regular q

def completeArea (v : Plane) : Measure (CompleteOrbits q v) :=
  (NativeRegularArea.regularArea q).comap Subtype.val

theorem completeArea_apply (v : Plane) (V : Set (CompleteOrbits q v)) :
    completeArea q v V = NativeRegularArea.regularArea q (Subtype.val '' V) :=
  comap_subtype_coe_apply (completeOrbitSet_measurable q v) _ V

theorem completeArea_univ (v : Plane) : completeArea q v univ =
    NativeRegularArea.regularArea q (completeOrbitSet q v) := by
  rw [completeArea_apply, image_univ, Subtype.range_coe]

theorem completeArea_univ_le (v : Plane) :
    completeArea q v univ ≤ NativeRegularArea.regularArea q univ := by
  rw [completeArea_univ]
  exact measure_mono (subset_univ _)
theorem complete_inclusion_measurePreserving (v : Plane) :
    MeasurePreserving (Subtype.val : CompleteOrbits q v → R)
      (completeArea q v)
      ((NativeRegularArea.regularArea q).restrict (completeOrbitSet q v)) where
  measurable := measurable_subtype_coe
  map_eq := map_comap_subtype_coe (completeOrbitSet_measurable q v) _

theorem timeMap_image_area (v : Plane) (t : ℝ) (A : Set (CompleteOrbits q v))
    (hA : MeasurableSet A) :
    completeArea q v (timeMap q v t '' A) = completeArea q v A := by
  have hMeas : MeasurableSet ((Subtype.val : CompleteOrbits q v → R) '' A) :=
    (MeasurableEmbedding.subtype_coe (completeOrbitSet_measurable q v)).measurableSet_image.mpr hA
  have hsource : (Subtype.val : CompleteOrbits q v → R) '' A ⊆
      (NativePartialDirectionalFlow.timeMap q v t).source := by
    rintro x ⟨y, hy, rfl⟩
    exact complete_time_mem q v y t
  have himage : (Subtype.val : CompleteOrbits q v → R) '' (timeMap q v t '' A) =
      NativePartialDirectionalFlow.timeMap q v t '' (Subtype.val '' A) := by
    rw [image_image, image_image]
    apply image_congr
    intro x hx
    exact timeMap_value q v t x
  rw [completeArea_apply, completeArea_apply, himage]
  exact NativePartialDirectionalArea.timeMap_image_area q v t _ hMeas hsource

theorem measurePreserving_timeMap (v : Plane) (t : ℝ) :
    MeasurePreserving (timeMap q v t) (completeArea q v) (completeArea q v) := by
  have hmeas := measurable_timeMap q v t
  refine ⟨hmeas, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hmeas hB]
  have himage : timeMap q v t '' (timeMap q v t ⁻¹' B) = B :=
    (timeEquiv q v t).surjective.image_preimage B
  have harea := timeMap_image_area q v t (timeMap q v t ⁻¹' B) (hB.preimage hmeas)
  rw [himage] at harea
  exact harea.symm

theorem completeArea_invariant (v : Plane) :
    letI := completeAction q v
    VAddInvariantMeasure ℝ (CompleteOrbits q v) (completeArea q v) := by
  let := completeAction q v
  constructor
  intro t B hB
  change completeArea q v (timeMap q v t ⁻¹' B) = completeArea q v B
  exact (measurePreserving_timeMap q v t).measure_preimage hB.nullMeasurableSet

def normalizedCompleteArea (v : Plane) : Measure (CompleteOrbits q v) :=
  (NativeRegularArea.regularArea q univ)⁻¹ • completeArea q v

theorem normalized_timeMap_measurePreserving (v : Plane) (t : ℝ) :
    MeasurePreserving (timeMap q v t)
      (normalizedCompleteArea q v) (normalizedCompleteArea q v) where
  measurable := measurable_timeMap q v t
  map_eq := by
    rw [normalizedCompleteArea, Measure.map_smul, (measurePreserving_timeMap q v t).map_eq]
    exact (measurable_timeMap q v t).aemeasurable

theorem normalizedCompleteArea_invariant (v : Plane) :
    letI := completeAction q v
    VAddInvariantMeasure ℝ (CompleteOrbits q v) (normalizedCompleteArea q v) := by
  let := completeAction q v
  constructor
  intro t B hB
  change normalizedCompleteArea q v (timeMap q v t ⁻¹' B) = normalizedCompleteArea q v B
  exact (normalized_timeMap_measurePreserving q v t).measure_preimage hB.nullMeasurableSet

end MNEC.NativeCompleteDirectionalArea



