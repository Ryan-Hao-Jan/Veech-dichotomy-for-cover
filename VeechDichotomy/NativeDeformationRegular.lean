module

public import VeechDichotomy.WholeDeformedDifferential
public import MNEC.TranslationLinearChartDerivatives

/-! The actual regular homeomorphism from a native differential to its
constructed compact SL2 deformation. Its constant physical derivative
and inverse derivative are derived from genuine primitive-coordinate
identities, not assumed as deformation data.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativeDeformationRegular

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveTransitions LinearGroup LinearEquivalences WholeDeformedAtlas
open Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

abbrev transformed := WholeDeformedDifferential.form q A

def regularHomeomorph : Regular q ≃ₜ Regular (transformed q A) :=
  (toOriginal q A).symm.subtype
    (p := fun x => x ∈ regularSet q) (q := fun y => y ∈ regularSet (transformed q A)) (by
      intro x
      rw [WholeDeformedDifferential.regularSet_form]
      rfl)

theorem regularHomeomorph_value (x : Regular q) :
    (regularHomeomorph q A x).val = (toOriginal q A).symm x.val := rfl

def oldPowerPrimitive (x : Regular q) : PrimitiveChart q x where
  chart := (powerAt q x.val).chart
  center := (powerAt q x.val).center
  regular_source := by
    intro y hy hzero
    have h := (powerAt q x.val).zero_in_source_eq_center hy hzero
    exact x.property (h ▸ hzero)
  derivative y hy := by
    have h := (powerAt q x.val).primitive_derivative y hy
    apply h.congr_of_eventuallyEq_abuse
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      rw [(powerAt q x.val).regular_center_exponent_one x.property, pow_one])

def newPowerPrimitive (x : Regular q) : PrimitiveChart (transformed q A) (regularHomeomorph q A x) where
  chart := WholeDeformedAtlas.chart q A ⟨x.val⟩
  center := WholeDeformedAtlas.chart_center q A ⟨x.val⟩
  regular_source := by
    intro y hy
    rw [WholeDeformedDifferential.regularSet_form]
    intro hzero
    have h := (powerAt q x.val).zero_in_source_eq_center hy hzero
    exact x.property (h ▸ hzero)
  derivative y hy := by
    have h := WholeDeformedDifferential.chartPower_hasMFDerivAt q A ⟨x.val⟩ y hy
    apply h.congr_of_eventuallyEq_abuse
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      rw [(powerAt q x.val).regular_center_exponent_one x.property, pow_one])

theorem powerPrimitive_relation (x y : Regular q) :
    (newPowerPrimitive q A x).chart (regularHomeomorph q A y).val =
      SL2PowerLift.complexAction A ((oldPowerPrimitive q x).chart y.val) := by
  have h := WholeDeformedAtlas.chart_power q A ⟨x.val⟩ (regularHomeomorph q A y).val
  simpa only [(powerAt q x.val).regular_center_exponent_one x.property, pow_one] using! h

theorem primitive_affine_germ (x : Regular q) :
    ∃ a : Plane, ∀ᶠ y in 𝓝 x,
      coordinateChart (transformed q A) (regularHomeomorph q A x) (regularHomeomorph q A y) =
        planeEquiv A (coordinateChart q x y) + a := by
  let P := oldPowerPrimitive q x
  let Q := newPowerPrimitive q A x
  let S := primitiveChart q x
  let T := primitiveChart (transformed q A) (regularHomeomorph q A x)
  let c := P.chart x.val - S x.val
  let d := T (regularHomeomorph q A x).val - Q.chart (regularHomeomorph q A x).val
  have hOld := MNEC.NativePrimitiveTransitions.difference_germ q S P.chart
    (MNEC.NativePrimitiveTransitions.chosen q x).derivative P.derivative x.val
    ⟨(MNEC.NativePrimitiveTransitions.chosen q x).center, P.center⟩
  have hNew := MNEC.NativePrimitiveTransitions.difference_germ (transformed q A) Q.chart T
    Q.derivative (MNEC.NativePrimitiveTransitions.chosen (transformed q A) (regularHomeomorph q A x)).derivative
    (regularHomeomorph q A x).val
    ⟨Q.center, (MNEC.NativePrimitiveTransitions.chosen (transformed q A) (regularHomeomorph q A x)).center⟩
  have hOldReg := (continuous_subtype_val : Continuous (Subtype.val : Regular q → X)).continuousAt hOld
  have hNewReg := (continuous_subtype_val.comp (regularHomeomorph q A).continuous).continuousAt hNew
  refine ⟨planeEquiv A (toPlane c) + toPlane d, ?_⟩
  filter_upwards [hOldReg, hNewReg] with y hyOld hyNew
  change P.chart y.val = S y.val + c at hyOld
  change T (regularHomeomorph q A y).val = Q.chart (regularHomeomorph q A y).val + d at hyNew
  have hcomplex : T (regularHomeomorph q A y).val =
      SL2PowerLift.complexAction A (S y.val + c) + d := by
    rw [hyNew, powerPrimitive_relation, hyOld]
  have hplane := congrArg toPlane hcomplex
  simpa only [coordinateChart_apply, SL2PowerLift.complexAction, map_add,
    ContinuousLinearEquiv.apply_symm_apply, add_assoc, S, T] using hplane

local instance : ChartedSpace Plane (Regular q) := MNEC.NativeRegularTranslationAtlas.chartedSpace q
local instance : ChartedSpace Plane (Regular (transformed q A)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed q A)
local instance : HasGroupoid (Regular q) MNEC.TranslationGroupoid.groupoid :=
  MNEC.NativeRegularTranslationAtlas.has_translation_groupoid q
local instance : HasGroupoid (Regular (transformed q A)) MNEC.TranslationGroupoid.groupoid :=
  MNEC.NativeRegularTranslationAtlas.has_translation_groupoid (transformed q A)
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := MNEC.NativeRegularTranslationAtlas.isManifold q ∞
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular (transformed q A)) :=
  MNEC.NativeRegularTranslationAtlas.isManifold (transformed q A) ∞

theorem coordinate_hasFDerivAt (x : Regular q) :
    HasFDerivAt (MNEC.TranslationLinearChartDerivatives.coordinate (regularHomeomorph q A)
      (coordinateChart q x) (coordinateChart (transformed q A) (regularHomeomorph q A x)))
      (planeEquiv A).toContinuousLinearMap (coordinateChart q x x) := by
  obtain ⟨a, ha⟩ := primitive_affine_germ q A x
  let B := coordinateChart q x
  have hx : x ∈ B.source := coordinateChart_center q x
  have hc := B.symm.continuousAt (B.map_source hx)
  have ht : Tendsto B.symm (𝓝 (B x)) (𝓝 x) := by
    simpa only [B.left_inv hx] using hc.tendsto
  have hnear := ht ha
  have heq : MNEC.TranslationLinearChartDerivatives.coordinate (regularHomeomorph q A)
      (coordinateChart q x) (coordinateChart (transformed q A) (regularHomeomorph q A x)) =ᶠ[𝓝 (B x)]
      (fun p : Plane => planeEquiv A p + a) := by
    filter_upwards [B.open_target.mem_nhds (B.map_source hx), hnear] with p hp hval
    change coordinateChart (transformed q A) (regularHomeomorph q A x)
      (regularHomeomorph q A (B.symm p)) = _
    change coordinateChart (transformed q A) (regularHomeomorph q A x)
      (regularHomeomorph q A (B.symm p)) = planeEquiv A (B (B.symm p)) + a at hval
    rwa [B.right_inv hp] at hval
  exact (((planeEquiv A).toContinuousLinearMap.hasFDerivAt).add_const a).congr_of_eventuallyEq heq

theorem hasMFDerivAt_regularHomeomorph (x : Regular q) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A) x
      (planeEquiv A).toContinuousLinearMap :=
  MNEC.TranslationLinearChartDerivatives.hasMFDerivAt_of_coordinate
    (regularHomeomorph q A) (planeEquiv A)
    (coordinateChart q x) (coordinateChart (transformed q A) (regularHomeomorph q A x))
    (show coordinateChart q x ∈ atlas Plane (Regular q) from ⟨x, rfl⟩)
    (show coordinateChart (transformed q A) (regularHomeomorph q A x) ∈
      atlas Plane (Regular (transformed q A)) from ⟨regularHomeomorph q A x, rfl⟩)
    x (coordinateChart_center q x) (coordinateChart_center (transformed q A) (regularHomeomorph q A x))
    (coordinate_hasFDerivAt q A x)

theorem hasMFDerivAt_regularHomeomorph_symm (y : Regular (transformed q A)) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularHomeomorph q A).symm y
      (planeEquiv A).symm.toContinuousLinearMap := by
  have h := MNEC.TranslationLinearChartDerivatives.hasMFDerivAt_symm_of_coordinate
    (regularHomeomorph q A) (planeEquiv A)
    (coordinateChart q ((regularHomeomorph q A).symm y))
    (coordinateChart (transformed q A) (regularHomeomorph q A ((regularHomeomorph q A).symm y)))
    (show coordinateChart q ((regularHomeomorph q A).symm y) ∈ atlas Plane (Regular q)
      from ⟨(regularHomeomorph q A).symm y, rfl⟩)
    (show coordinateChart (transformed q A) (regularHomeomorph q A ((regularHomeomorph q A).symm y)) ∈
      atlas Plane (Regular (transformed q A)) from ⟨regularHomeomorph q A ((regularHomeomorph q A).symm y), rfl⟩)
    ((regularHomeomorph q A).symm y) (coordinateChart_center q _)
    (by simpa only [Homeomorph.apply_symm_apply] using coordinateChart_center (transformed q A) y)
    (coordinate_hasFDerivAt q A ((regularHomeomorph q A).symm y))
  simpa only [Homeomorph.apply_symm_apply] using! h

end VeechDichotomy.NativeDeformationRegular
