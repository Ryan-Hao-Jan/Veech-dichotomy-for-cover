module

public import MNEC.NativeRegularArea
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-! Intrinsic physical area on the WHOLE original native complex curve.
It is the actual canonical primitive-chart area pushed through the regular
inclusion, with the finite zero set assigned mass zero. Exact inclusion,
chart-image and nonatomicity formulas are proved; finite total mass and
normalized probability are separate analytic obligations. -/

@[expose] public section
noncomputable section
namespace MNEC.NativePhysicalArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas MeasureTheory Set
open scoped Classical Manifold ContDiff Topology

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem regularArea_singleton (q : Differential X) (x : Regular q) :
    NativeRegularArea.regularArea q {x} = 0 := by
  let : NullSingletonClass (volume : Measure Plane) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  rw [NativeRegularArea.coordinateChart_formula q x {x} (measurableSet_singleton x)
    (singleton_subset_iff.mpr (coordinateChart_center q x)), image_singleton]
  exact measure_singleton _

theorem regularArea_nullSingleton (q : Differential X) :
    NullSingletonClass (NativeRegularArea.regularArea q) := ⟨regularArea_singleton q⟩

def surfaceArea (q : Differential X) : Measure X :=
  (NativeRegularArea.regularArea q).map (Subtype.val : Regular q → X)

theorem surfaceArea_apply (q : Differential X) (A : Set X) (hA : MeasurableSet A) :
    surfaceArea q A = NativeRegularArea.regularArea q ((Subtype.val : Regular q → X) ⁻¹' A) :=
  Measure.map_apply measurable_subtype_coe hA

theorem regular_inclusion_measurePreserving (q : Differential X) :
    MeasurePreserving (Subtype.val : Regular q → X) (NativeRegularArea.regularArea q) (surfaceArea q) :=
  ⟨measurable_subtype_coe, rfl⟩

theorem surfaceArea_univ (q : Differential X) : surfaceArea q univ = NativeRegularArea.regularArea q univ := by
  rw [surfaceArea_apply q univ MeasurableSet.univ, preimage_univ]

theorem surfaceArea_zeroSet (q : Differential X) : surfaceArea q (zeroSet q) = 0 := by
  rw [surfaceArea_apply q (zeroSet q) (zeroSet_closed q).measurableSet]
  have hpre : (Subtype.val : Regular q → X) ⁻¹' zeroSet q = ∅ := by
    ext x
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    exact x.property
  rw [hpre, measure_empty]

theorem surfaceArea_regular_image (q : Differential X) (A : Set (Regular q)) (hA : MeasurableSet A) :
    surfaceArea q ((Subtype.val : Regular q → X) '' A) = NativeRegularArea.regularArea q A := by
  have hme : MeasurableEmbedding (Subtype.val : Regular q → X) :=
    MeasurableEmbedding.subtype_coe (regularSet_open q).measurableSet
  rw [surfaceArea_apply q _ (hme.measurableSet_image.mpr hA),
    preimage_image_eq A Subtype.val_injective]

theorem surfaceArea_regularSet (q : Differential X) :
    surfaceArea q (regularSet q) = NativeRegularArea.regularArea q univ := by
  have h := surfaceArea_regular_image q univ MeasurableSet.univ
  simpa only [image_univ, Subtype.range_coe] using h

theorem surfaceArea_singleton (q : Differential X) (p : X) : surfaceArea q {p} = 0 := by
  rw [surfaceArea_apply q {p} (measurableSet_singleton p)]
  by_cases hp : p ∈ regularSet q
  · let x : Regular q := ⟨p, hp⟩
    have hpre : (Subtype.val : Regular q → X) ⁻¹' {p} = {x} := by
      ext y
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [hpre, regularArea_singleton]
  · have hpre : (Subtype.val : Regular q → X) ⁻¹' {p} = ∅ := by
      ext y
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro h
      exact hp (h ▸ y.property)
    rw [hpre, measure_empty]

theorem surfaceArea_nullSingleton (q : Differential X) : NullSingletonClass (surfaceArea q) :=
  ⟨surfaceArea_singleton q⟩

end MNEC.NativePhysicalArea

