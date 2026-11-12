module

public import VeechDichotomy.NativeDeformationFlow
public import MNEC.NativeProbabilityArea
public import MNEC.LocalPhysicalAreaTransport
public import MNEC.TranslationVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Flat area is preserved by the constructed compact SL2 deformation.
Local native affine chart identities and det(A)=1 give the local measure
formula. A derived countable cover glues it on the regular locus, and the
canonical whole-curve area follows by the actual regular inclusions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativeDeformationArea

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeDeformationRegular LinearGroup LinearEquivalences WholeDeformedAtlas
open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Classical ENNReal

theorem volume_linear (A : SL2) (B : Set Plane) : volume (planeEquiv A '' B) = volume B := by
  let : (volume : Measure Plane).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  have h := (volume : Measure Plane).addHaar_image_continuousLinearEquiv (planeEquiv A) B
  simpa only [planeEquiv_det, abs_one, ENNReal.ofReal_one, one_mul] using h

def affineHomeomorph (A : SL2) (a : Plane) : Plane ≃ₜ Plane :=
  (planeEquiv A).toHomeomorph.trans (Homeomorph.addRight a)

theorem volume_affine (A : SL2) (a : Plane) (B : Set Plane) :
    volume (affineHomeomorph A a '' B) = volume B := by
  have heq : affineHomeomorph A a '' B = (fun p : Plane => p + a) '' (planeEquiv A '' B) := by
    rw [image_image]
    rfl
  rw [heq, MNEC.TranslationVolume.volume_translation, volume_linear]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩
local instance : MeasurableSpace (WholeSurface q A) := borel (WholeSurface q A)
local instance : BorelSpace (WholeSurface q A) := ⟨rfl⟩

def localModel (x : Regular q) (a : Plane) : OpenPartialHomeomorph (Regular q) (Regular (transformed q A)) :=
  ((coordinateChart q x).transHomeomorph (affineHomeomorph A a)).trans
    (coordinateChart (transformed q A) (regularHomeomorph q A x)).symm

theorem localModel_image_area (x : Regular q) (a : Plane)
    (V : Set (Regular q)) (hV : MeasurableSet V) (hsub : V ⊆ (localModel q A x a).source) :
    MNEC.NativeRegularArea.regularArea (transformed q A) (localModel q A x a '' V) =
      MNEC.NativeRegularArea.regularArea q V := by
  let B := coordinateChart (transformed q A) (regularHomeomorph q A x)
  let C := coordinateChart q x
  let E := localModel q A x a
  have hVsource : V ⊆ C.source := fun y hy => (hsub hy).1
  have hImageMeas : MeasurableSet (E '' V) :=
    MNEC.LocalPhysicalAreaTransport.measurableSet_image_of_subset_source E V hV hsub
  have hImageSource : E '' V ⊆ B.source := by
    rintro y ⟨z, hz, rfl⟩
    exact B.map_target (hsub hz).2
  have himage : B '' (E '' V) = affineHomeomorph A a '' (C '' V) := by
    ext p
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨C z, ⟨z, hz, rfl⟩, (B.right_inv (hsub hz).2).symm⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨E z, ⟨z, hz, rfl⟩, B.right_inv (hsub hz).2⟩
  rw [MNEC.NativeRegularArea.coordinateChart_formula _ _ _ hImageMeas hImageSource,
    himage, volume_affine, ← MNEC.NativeRegularArea.coordinateChart_formula q x V hV hVsource]

theorem image_area (V : Set (Regular q)) (hV : MeasurableSet V) :
    MNEC.NativeRegularArea.regularArea (transformed q A) (regularHomeomorph q A '' V) =
      MNEC.NativeRegularArea.regularArea q V := by
  let : SecondCountableTopology (Regular q) := secondCountableRegular q
  have hdata : ∀ x : Regular q, ∃ (a : Plane) (U : Set (Regular q)),
      IsOpen U ∧ x ∈ U ∧ U ⊆ (localModel q A x a).source ∧
        EqOn (regularHomeomorph q A) (localModel q A x a) U := by
    intro x
    obtain ⟨a, ha⟩ := primitive_affine_germ q A x
    let B := coordinateChart (transformed q A) (regularHomeomorph q A x)
    let C := coordinateChart q x
    let E := localModel q A x a
    have hxB : regularHomeomorph q A x ∈ B.source := coordinateChart_center (transformed q A) _
    have hxE : x ∈ E.source := by
      refine ⟨coordinateChart_center q x, ?_⟩
      change planeEquiv A (C x) + a ∈ B.target
      rw [← ha.self_of_nhds]
      exact B.map_source hxB
    have hEq : ∀ᶠ y in 𝓝 x, regularHomeomorph q A y = E y := by
      filter_upwards [ha, (regularHomeomorph q A).continuous.continuousAt
        (B.open_source.mem_nhds hxB)] with y hy hyB
      change regularHomeomorph q A y = B.symm (planeEquiv A (C y) + a)
      rw [← hy, B.left_inv hyB]
    have hBoth : ∀ᶠ y in 𝓝 x, y ∈ E.source ∧ regularHomeomorph q A y = E y := by
      filter_upwards [E.open_source.mem_nhds hxE, hEq] with y hy heq
      exact ⟨hy, heq⟩
    obtain ⟨U, hUs, hU, hxU⟩ := _root_.mem_nhds_iff.mp hBoth
    exact ⟨a, U, hU, hxU, fun y hy => (hUs hy).1, fun y hy => (hUs hy).2⟩
  choose a U hU hxU hsource hEq using hdata
  let F := (regularHomeomorph q A).toOpenPartialHomeomorph
  have hcover : F.source ⊆ ⋃ x : Regular q, U x := fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩
  exact MNEC.LocalPhysicalAreaTransport.image_area_of_open_cover
    (MNEC.NativeRegularArea.regularArea q) (MNEC.NativeRegularArea.regularArea (transformed q A))
    F U (fun x => localModel q A x (a x)) hU hcover hsource hEq
    (fun x => localModel_image_area q A x (a x)) V hV (subset_univ _)

theorem regular_measurePreserving : MeasurePreserving (regularHomeomorph q A)
    (MNEC.NativeRegularArea.regularArea q) (MNEC.NativeRegularArea.regularArea (transformed q A)) where
  measurable := (regularHomeomorph q A).measurable
  map_eq := by
    apply Measure.ext
    intro B hB
    rw [Measure.map_apply (regularHomeomorph q A).measurable hB]
    have h := image_area q A (regularHomeomorph q A ⁻¹' B)
      (hB.preimage (regularHomeomorph q A).measurable)
    rw [Set.image_preimage_eq B (regularHomeomorph q A).surjective] at h
    exact h.symm

theorem regularArea_univ :
    MNEC.NativeRegularArea.regularArea (transformed q A) univ = MNEC.NativeRegularArea.regularArea q univ := by
  have h := image_area q A univ MeasurableSet.univ
  simpa only [image_univ, (regularHomeomorph q A).surjective.range_eq] using h

theorem totalArea_eq :
    MNEC.NativeFiniteRegularArea.totalArea (transformed q A) = MNEC.NativeFiniteRegularArea.totalArea q :=
  congrArg ENNReal.toReal (regularArea_univ q A)

theorem surface_measurePreserving : MeasurePreserving (toOriginal q A).symm
    (MNEC.NativePhysicalArea.surfaceArea q) (MNEC.NativePhysicalArea.surfaceArea (transformed q A)) where
  measurable := (toOriginal q A).symm.measurable
  map_eq := by
    change ((MNEC.NativeRegularArea.regularArea q).map (Subtype.val : Regular q → X)).map
      (toOriginal q A).symm =
        (MNEC.NativeRegularArea.regularArea (transformed q A)).map
          (Subtype.val : Regular (transformed q A) → WholeSurface q A)
    rw [Measure.map_map (toOriginal q A).symm.measurable measurable_subtype_coe]
    have heq : (toOriginal q A).symm ∘ (Subtype.val : Regular q → X) =
        (Subtype.val : Regular (transformed q A) → WholeSurface q A) ∘ regularHomeomorph q A :=
      funext (fun x => (regularHomeomorph_value q A x).symm)
    rw [heq, ← Measure.map_map measurable_subtype_coe (regularHomeomorph q A).measurable,
      (regular_measurePreserving q A).map_eq]

theorem normalized_regular_measurePreserving : MeasurePreserving (regularHomeomorph q A)
    (MNEC.NativeProbabilityArea.normalizedRegularArea q)
    (MNEC.NativeProbabilityArea.normalizedRegularArea (transformed q A)) := by
  have h := (regular_measurePreserving q A).smul_measure
    (MNEC.NativeRegularArea.regularArea q univ)⁻¹
  simpa only [MNEC.NativeProbabilityArea.normalizedRegularArea, regularArea_univ] using h

theorem normalized_surface_measurePreserving : MeasurePreserving (toOriginal q A).symm
    (MNEC.NativeProbabilityArea.normalizedArea q)
    (MNEC.NativeProbabilityArea.normalizedArea (transformed q A)) := by
  have h := (surface_measurePreserving q A).smul_measure
    (MNEC.NativeRegularArea.regularArea q univ)⁻¹
  simpa only [MNEC.NativeProbabilityArea.normalizedArea, regularArea_univ] using h

end VeechDichotomy.NativeDeformationArea
