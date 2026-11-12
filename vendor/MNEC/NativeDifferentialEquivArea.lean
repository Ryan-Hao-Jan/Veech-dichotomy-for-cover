module

public import MNEC.NativeDifferentialEquiv
public import MNEC.NativeProbabilityArea

/-! Canonical native physical area is preserved by a genuine isomorphism
of holomorphic differentials. Only the actual curve homeomorphism, complex
differentiability and literal one-form pullback are supplied. Every area
identity is derived from the intrinsic primitive-chart measure formulas. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeDifferentialEquivArea

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas
open NativeDifferentialEquiv MeasureTheory Set Topology
open scoped Manifold ContDiff ENNReal Classical

set_option autoImplicit false

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩
local instance : MeasurableSpace Y := borel Y
local instance : BorelSpace Y := ⟨rfl⟩

variable {q : Differential X} {r : Differential Y}

def pulledIndex (e : Equiv q r) (x : Regular q) : NativePrimitiveAreaCharts.Index q :=
  ⟨x, pulledPrimitive e x⟩

theorem pulled_chart_source (e : Equiv q r) (x : Regular q) :
    (NativePrimitiveAreaCharts.chart q (pulledIndex e x)).source =
      regularHomeomorph e ⁻¹' (coordinateChart r (regularHomeomorph e x)).source := by
  ext y
  rw [NativePrimitiveAreaCharts.chart_source, coordinateChart_source]
  change (y.val ∈ (e.homeomorph.toOpenPartialHomeomorph.trans
    (NativePrimitiveTransitions.chosen r (regularHomeomorph e x)).chart).source) ↔ _
  simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    univ_inter, mem_preimage, regularHomeomorph_value, primitiveChart]
  rfl

theorem pulled_chart_apply (e : Equiv q r) (x y : Regular q) :
    NativePrimitiveAreaCharts.chart q (pulledIndex e x) y =
      coordinateChart r (regularHomeomorph e x) (regularHomeomorph e y) := rfl

def pulledArea (e : Equiv q r) : Measure (Regular q) :=
  (NativeRegularArea.regularArea r).comap (regularHomeomorph e)

theorem pulledArea_chart (e : Equiv q r) (x : Regular q) (A : Set (Regular q))
    (hA : MeasurableSet A)
    (hsub : A ⊆ (NativePrimitiveAreaCharts.chart q (pulledIndex e x)).source) :
    pulledArea e A = volume (NativePrimitiveAreaCharts.chart q (pulledIndex e x) '' A) := by
  let H := regularHomeomorph e
  have hHA : MeasurableSet (H '' A) := H.measurableEmbedding.measurableSet_image.mpr hA
  have hHs : H '' A ⊆ (coordinateChart r (H x)).source := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hsub hy
    rw [pulled_chart_source] at h
    exact h
  have himage : coordinateChart r (H x) '' (H '' A) =
      NativePrimitiveAreaCharts.chart q (pulledIndex e x) '' A := by
    rw [image_image]
    apply image_congr
    intro y _
    exact (pulled_chart_apply e x y).symm
  rw [pulledArea, H.measurableEmbedding.comap_apply,
    NativeRegularArea.coordinateChart_formula r _ _ hHA hHs, himage]

theorem regularArea_pullback_eq (e : Equiv q r) :
    pulledArea e = NativeRegularArea.regularArea q := by
  let c : Regular q → OpenPartialHomeomorph (Regular q) Plane :=
    fun x => NativePrimitiveAreaCharts.chart q (pulledIndex e x)
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  let : Nonempty (Regular q) := regular_nonempty q
  have hcover : ∀ x : Regular q, ∃ i : Regular q, x ∈ (c i).source := by
    intro x
    refine ⟨x, ?_⟩
    rw [NativePrimitiveAreaCharts.chart_source]
    exact (pulledPrimitive e x).center
  obtain ⟨C⟩ := TranslationAtlasMeasure.exists_cover c hcover
  have hPull : pulledArea e = TranslationAtlasMeasure.area c C :=
    TranslationAtlasMeasure.unique c C _ (fun x A hA hsub => pulledArea_chart e x A hA hsub)
  exact hPull.trans (NativeRegularArea.gluing_independent q (pulledIndex e) C)

theorem regularHomeomorph_measurePreserving (e : Equiv q r) :
    MeasurePreserving (regularHomeomorph e)
      (NativeRegularArea.regularArea q) (NativeRegularArea.regularArea r) := by
  let H := regularHomeomorph e
  refine ⟨H.measurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply H.measurable hB, ← regularArea_pullback_eq e, pulledArea,
    H.measurableEmbedding.comap_apply, image_preimage_eq _ H.surjective]

theorem regularArea_univ_eq (e : Equiv q r) :
    NativeRegularArea.regularArea q univ = NativeRegularArea.regularArea r univ := by
  have h := (regularHomeomorph_measurePreserving e).measure_preimage
    MeasurableSet.univ.nullMeasurableSet
  simpa only [preimage_univ] using h

theorem totalArea_eq (e : Equiv q r) :
    NativeFiniteRegularArea.totalArea q = NativeFiniteRegularArea.totalArea r := by
  unfold NativeFiniteRegularArea.totalArea
  rw [regularArea_univ_eq e]

theorem homeomorph_surfaceArea_measurePreserving (e : Equiv q r) :
    MeasurePreserving e.homeomorph (NativePhysicalArea.surfaceArea q)
      (NativePhysicalArea.surfaceArea r) := by
  have h := (NativePhysicalArea.regular_inclusion_measurePreserving r).comp
    (regularHomeomorph_measurePreserving e)
  refine ⟨e.homeomorph.measurable, ?_⟩
  rw [NativePhysicalArea.surfaceArea, Measure.map_map e.homeomorph.measurable
    measurable_subtype_coe]
  exact h.map_eq

theorem normalized_regular_measurePreserving (e : Equiv q r) :
    MeasurePreserving (regularHomeomorph e)
      (NativeProbabilityArea.normalizedRegularArea q)
      (NativeProbabilityArea.normalizedRegularArea r) := by
  unfold NativeProbabilityArea.normalizedRegularArea
  rw [regularArea_univ_eq e]
  exact (regularHomeomorph_measurePreserving e).smul_measure _

theorem normalized_surface_measurePreserving (e : Equiv q r) :
    MeasurePreserving e.homeomorph (NativeProbabilityArea.normalizedArea q)
      (NativeProbabilityArea.normalizedArea r) := by
  unfold NativeProbabilityArea.normalizedArea
  rw [regularArea_univ_eq e]
  exact (homeomorph_surfaceArea_measurePreserving e).smul_measure _

end MNEC.NativeDifferentialEquivArea

