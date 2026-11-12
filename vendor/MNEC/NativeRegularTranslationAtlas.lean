module

public import MNEC.NativePrimitiveTransitions
public import MNEC.TranslationGroupoid
public import Mathlib.Geometry.Manifold.HasGroupoid
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Complex.Basic

/-! The actual regular locus of an arbitrary native nonzero holomorphic
form has a constructed real physical translation atlas. Primitive charts
come from analytic primitives and the complex inverse function theorem;
compatibility is proved from the intrinsic form identity. No splitting,
atlas, groupoid, smoothness or flow certificate is an input. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeRegularTranslationAtlas

open LatticeTorus NativeAbelianDifferential NativePrimitiveTransitions Set Filter Topology
open scoped Manifold ContDiff Classical
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

abbrev Regular (q : Differential X) := ↥(regularSet q)

def regularOpen (q : Differential X) : TopologicalSpace.Opens X := ⟨regularSet q, regularSet_open q⟩

theorem regular_nonempty (q : Differential X) : Nonempty (Regular q) :=
  (regularSet_nonempty q).to_subtype

def primitiveChart (q : Differential X) (i : Regular q) : OpenPartialHomeomorph X ℂ := (chosen q i).chart

def complexChart (q : Differential X) (i : Regular q) : OpenPartialHomeomorph (Regular q) ℂ :=
  (primitiveChart q i).subtypeRestr (s := regularOpen q) (regular_nonempty q)

theorem complexChart_source (q : Differential X) (i : Regular q) :
    (complexChart q i).source = Subtype.val ⁻¹' (primitiveChart q i).source := by
  exact (primitiveChart q i).subtypeRestr_source (s := regularOpen q) (regular_nonempty q)

theorem complexChart_apply (q : Differential X) (i x : Regular q) :
    complexChart q i x = primitiveChart q i x.val := rfl

theorem complexChart_target (q : Differential X) (i : Regular q) :
    (complexChart q i).target = (primitiveChart q i).target := by
  apply Subset.antisymm
  · exact (primitiveChart q i).subtypeRestr_target_subset _
  · intro z hz
    let y : Regular q := ⟨(primitiveChart q i).symm z, (chosen q i).regular_source ((primitiveChart q i).map_target hz)⟩
    have hy : y.val ∈ (primitiveChart q i).source := (primitiveChart q i).map_target hz
    have hmem := (primitiveChart q i).map_subtype_source (s := regularOpen q) (regular_nonempty q) (x := y) hy
    have heq : primitiveChart q i y.val = z := (primitiveChart q i).right_inv hz
    rwa [heq] at hmem

def toPlane : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM

def coordinateChart (q : Differential X) (i : Regular q) : OpenPartialHomeomorph (Regular q) Plane :=
  (complexChart q i).transHomeomorph toPlane.toHomeomorph

theorem coordinateChart_source (q : Differential X) (i : Regular q) :
    (coordinateChart q i).source = Subtype.val ⁻¹' (primitiveChart q i).source := complexChart_source q i

theorem coordinateChart_target (q : Differential X) (i : Regular q) :
    (coordinateChart q i).target = toPlane.symm ⁻¹' (primitiveChart q i).target := by
  change toPlane.symm ⁻¹' (complexChart q i).target = _
  rw [complexChart_target]

theorem coordinateChart_apply (q : Differential X) (i x : Regular q) :
    coordinateChart q i x = toPlane (primitiveChart q i x.val) := rfl

theorem coordinateChart_center (q : Differential X) (x : Regular q) : x ∈ (coordinateChart q x).source := by
  rw [coordinateChart_source]
  exact (chosen q x).center

theorem coordinateChart_symm_value (q : Differential X) (i : Regular q) (p : Plane)
    (hp : p ∈ (coordinateChart q i).target) :
    ((coordinateChart q i).symm p).val = (primitiveChart q i).symm (toPlane.symm p) := by
  let y := (coordinateChart q i).symm p
  have hy : y.val ∈ (primitiveChart q i).source := by
    have h := (coordinateChart q i).map_target hp
    rwa [coordinateChart_source] at h
  have heq : toPlane (primitiveChart q i y.val) = p := (coordinateChart q i).right_inv hp
  have hraw : primitiveChart q i y.val = toPlane.symm p := by
    apply toPlane.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact heq
  calc
    y.val = (primitiveChart q i).symm (primitiveChart q i y.val) := ((primitiveChart q i).left_inv hy).symm
    _ = _ := by rw [hraw]

@[instance_reducible] def chartedSpace (q : Differential X) : ChartedSpace Plane (Regular q) where
  atlas := range (coordinateChart q)
  chartAt x := coordinateChart q x
  mem_chart_source x := coordinateChart_center q x
  chart_mem_atlas x := ⟨x, rfl⟩

theorem transition_locally_translation (q : Differential X) (i j : Regular q) :
    TranslationGroupoid.LocallyTranslationOn ((coordinateChart q i).symm.trans (coordinateChart q j))
      ((coordinateChart q i).symm.trans (coordinateChart q j)).source := by
  intro p hp
  have hp₁ : toPlane.symm p ∈ (primitiveChart q i).target := by
    have hpt : p ∈ (coordinateChart q i).target := hp.1
    rw [coordinateChart_target] at hpt
    exact hpt
  have hp₂ : (primitiveChart q i).symm (toPlane.symm p) ∈ (primitiveChart q j).source := by
    have h := hp.2
    rw [coordinateChart_source] at h
    change ((coordinateChart q i).symm p).val ∈ (primitiveChart q j).source at h
    rwa [coordinateChart_symm_value q i p hp.1] at h
  obtain ⟨a, ha⟩ := NativePrimitiveTransitions.transition_germ q (primitiveChart q i) (primitiveChart q j)
    (chosen q i).derivative (chosen q j).derivative (toPlane.symm p) ⟨hp₁, hp₂⟩
  refine ⟨toPlane a, ?_⟩
  have hc : ContinuousAt toPlane.symm p := toPlane.symm.continuous.continuousAt
  filter_upwards [((coordinateChart q i).symm.trans (coordinateChart q j)).open_source.mem_nhds hp, hc ha] with z hz htrans
  change toPlane (primitiveChart q j ((coordinateChart q i).symm z).val) = z + toPlane a
  rw [coordinateChart_symm_value q i z hz.1]
  change toPlane (((primitiveChart q i).symm.trans (primitiveChart q j)) (toPlane.symm z)) = _
  rw [htrans, map_add, ContinuousLinearEquiv.apply_symm_apply]

theorem has_translation_groupoid (q : Differential X) :
    letI := chartedSpace q
    HasGroupoid (Regular q) TranslationGroupoid.groupoid := by
  let := chartedSpace q
  apply hasGroupoid_of_pregroupoid TranslationGroupoid.pregroupoid
  intro e f he hf
  change e ∈ range (coordinateChart q) at he
  change f ∈ range (coordinateChart q) at hf
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := hf
  exact transition_locally_translation q i j

theorem contDiffAt_of_translation {f : Plane → Plane} {x : Plane} (n : ℕ∞ω)
    (h : ∃ a : Plane, ∀ᶠ y in 𝓝 x, f y = y + a) : ContDiffAt ℝ n f x := by
  obtain ⟨a, ha⟩ := h
  exact (contDiff_id.add contDiff_const).contDiffAt.congr_of_eventuallyEq ha

theorem translationGroupoid_le_contDiffGroupoid (n : ℕ∞ω) :
    TranslationGroupoid.groupoid ≤ contDiffGroupoid n 𝓘(ℝ, Plane) := by
  apply StructureGroupoid.le_iff.mpr
  intro e he
  have ht := (TranslationGroupoid.mem_groupoid_iff e).mp he
  change e ∈ (contDiffPregroupoid n 𝓘(ℝ, Plane)).groupoid
  rw [mem_groupoid_of_pregroupoid]
  constructor
  · simpa only [contDiffPregroupoid, mfld_simps] using
      (show ContDiffOn ℝ n e e.source from fun x hx => (contDiffAt_of_translation n (ht.1 x hx)).contDiffWithinAt)
  · simpa only [contDiffPregroupoid, mfld_simps] using
      (show ContDiffOn ℝ n e.symm e.target from fun x hx => (contDiffAt_of_translation n (ht.2 x hx)).contDiffWithinAt)

theorem isManifold (q : Differential X) (n : ℕ∞ω) :
    letI := chartedSpace q
    IsManifold 𝓘(ℝ, Plane) n (Regular q) := by
  let := chartedSpace q
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let : HasGroupoid (Regular q) (contDiffGroupoid n 𝓘(ℝ, Plane)) :=
    hasGroupoid_of_le (G₁ := TranslationGroupoid.groupoid) (by infer_instance) (translationGroupoid_le_contDiffGroupoid n)
  exact IsManifold.mk' 𝓘(ℝ, Plane) n (Regular q)

theorem secondCountableRegular (q : Differential X) : SecondCountableTopology (Regular q) := by
  let : SecondCountableTopology X := ChartedSpace.secondCountable_of_sigmaCompact ℂ X
  infer_instance

theorem locallyCompactRegular (q : Differential X) : LocallyCompactSpace (Regular q) := by
  let := chartedSpace q
  exact ChartedSpace.locallyCompactSpace (H := Plane) (M := Regular q)

end MNEC.NativeRegularTranslationAtlas
