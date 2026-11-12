module

public import VeechDichotomy.PhysicalDerivativeTranslation
public import MNEC.NativeDifferentialEquivCompletion
public import MNEC.NativePrimitiveInverse

/-! Identity physical derivatives on actual regular loci supply genuine
holomorphic differential equivalences of whole compact curves. The
holomorphicity and the intrinsic one-form pullback are derived, including
at the finite zero sets. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePhysicalDifferentialEquiv

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveTransitions Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {q : Differential X} {r : Differential Y}

theorem eventually_whole (x : Regular q) (P : X → Prop)
    (hP : ∀ᶠ y : Regular q in 𝓝 x, P y.val) : ∀ᶠ y in 𝓝 x.val, P y := by
  have hm : Filter.map (Subtype.val : Regular q → X) (𝓝 x) = 𝓝 x.val :=
    (regularSet_open q).isOpenMap_subtype_val.map_nhds_eq continuous_subtype_val.continuousAt
  rw [← hm]
  exact hP

local instance : ChartedSpace Plane (Regular q) := chartedSpace q
local instance : ChartedSpace Plane (Regular r) := chartedSpace r
local instance : HasGroupoid (Regular q) MNEC.TranslationGroupoid.groupoid := has_translation_groupoid q
local instance : HasGroupoid (Regular r) MNEC.TranslationGroupoid.groupoid := has_translation_groupoid r
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := isManifold q ∞
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular r) := isManifold r ∞

theorem primitive_translation_germ (H : X → Y) (R : Regular q → Regular r)
    (hc : Continuous R)
    (hvalue : ∀ x : Regular q, (R x).val = H x.val)
    (hD : ∀ x : Regular q, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) R x
      (ContinuousLinearMap.id ℝ Plane)) (x : Regular q) :
    ∃ a : ℂ, ∀ᶠ y in 𝓝 x.val, primitiveChart r (R x) (H y) = primitiveChart q x y + a := by
  obtain ⟨a, ha⟩ := PhysicalDerivativeTranslation.map_translation_germ R hc hD
    (coordinateChart q x) (coordinateChart r (R x))
    (show coordinateChart q x ∈ atlas Plane (Regular q) from ⟨x, rfl⟩)
    (show coordinateChart r (R x) ∈ atlas Plane (Regular r) from ⟨R x, rfl⟩)
    x (coordinateChart_center q x) (coordinateChart_center r (R x))
  refine ⟨toPlane.symm a, eventually_whole x _ ?_⟩
  filter_upwards [ha] with y hy
  have hc := congrArg toPlane.symm hy
  simpa only [coordinateChart_apply, map_add, ContinuousLinearEquiv.symm_apply_apply, hvalue] using hc

theorem mdifferentiableAt_of_primitive_germ (H : X → Y) (hc : Continuous H)
    (x : Regular q) (y : Regular r)
    (hxy : y.val = H x.val) (a : ℂ)
    (hg : ∀ᶠ z in 𝓝 x.val, primitiveChart r y (H z) = primitiveChart q x z + a) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H x.val := by
  let P := chosen q x
  let Q := chosen r y
  have hy : H x.val ∈ Q.chart.source := by rw [← hxy]; exact Q.center
  have ht : P.chart x.val + a ∈ Q.chart.target := by
    change primitiveChart q x x.val + a ∈ (primitiveChart r y).target
    rw [← hg.self_of_nhds]
    exact Q.chart.map_source hy
  have hInv := MNEC.NativePrimitiveInverse.symm_mdifferentiableAt r y Q _ ht
  have hAdd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : ℂ => z + a) (P.chart x.val) :=
    (differentiableAt_id.add_const a).mdifferentiableAt
  apply (hInv.comp x.val (hAdd.comp x.val (P.derivative x.val P.center).mdifferentiableAt)).congr_of_eventuallyEq
  filter_upwards [hg, hc.continuousAt (Q.chart.open_source.mem_nhds hy)] with z hz hzQ
  change H z = Q.chart.symm (P.chart z + a)
  change Q.chart (H z) = P.chart z + a at hz
  rw [← hz, Q.chart.left_inv hzQ]

theorem pullback_of_primitive_germ (H : X → Y) (hc : Continuous H)
    (x : Regular q) (y : Regular r)
    (hxy : y.val = H x.val) (a : ℂ)
    (hg : ∀ᶠ z in 𝓝 x.val, primitiveChart r y (H z) = primitiveChart q x z + a) :
    q.val.toFun x.val = (r.val.toFun (H x.val)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) H x.val) := by
  have hHol := mdifferentiableAt_of_primitive_germ H hc x y hxy a hg
  have hy : H x.val ∈ (chosen r y).chart.source := by rw [← hxy]; exact (chosen r y).center
  have hcomp := ((chosen r y).derivative _ hy).comp x.val hHol.hasMFDerivAt
  have htrans : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z : ℂ => z + a)
      ((chosen q x).chart x.val) (ContinuousLinearMap.id ℂ ℂ) :=
    ((hasFDerivAt_id _).add_const a).hasMFDerivAt
  have hsrc : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z => primitiveChart q x z + a) x.val
      (q.val.toFun x.val) := by
    simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using!
      htrans.comp x.val ((chosen q x).derivative _ (chosen q x).center)
  have htarget : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z => primitiveChart q x z + a) x.val
      ((r.val.toFun (H x.val)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) H x.val)) :=
    hcomp.congr_of_eventuallyEq_abuse (hg.mono fun _ h => h.symm)
  exact hsrc.mfderiv.symm.trans htarget.mfderiv

def of_physical_derivatives (H : X ≃ₜ Y) (R : Regular q ≃ₜ Regular r)
    (hvalue : ∀ x : Regular q, (R x).val = H x.val)
    (hD : ∀ x : Regular q, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) R x
      (ContinuousLinearMap.id ℝ Plane))
    (hInv : ∀ y : Regular r, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) R.symm y
      (ContinuousLinearMap.id ℝ Plane)) : MNEC.NativeDifferentialEquiv.Equiv q r := by
  have hvalueInv : ∀ y : Regular r, (R.symm y).val = H.symm y.val := by
    intro y
    apply H.injective
    rw [Homeomorph.apply_symm_apply, ← hvalue, Homeomorph.apply_symm_apply]
  refine MNEC.NativeDifferentialEquivCompletion.of_regular H R hvalue ?_ ?_ ?_
  · intro x hx
    obtain ⟨a, ha⟩ := primitive_translation_germ H R R.continuous hvalue hD ⟨x, hx⟩
    exact mdifferentiableAt_of_primitive_germ H H.continuous ⟨x, hx⟩ (R ⟨x, hx⟩) (hvalue _) a ha
  · intro y hy
    obtain ⟨a, ha⟩ := primitive_translation_germ H.symm R.symm R.symm.continuous hvalueInv hInv ⟨y, hy⟩
    exact mdifferentiableAt_of_primitive_germ H.symm H.symm.continuous ⟨y, hy⟩ (R.symm ⟨y, hy⟩) (hvalueInv _) a ha
  · intro x hx
    obtain ⟨a, ha⟩ := primitive_translation_germ H R R.continuous hvalue hD ⟨x, hx⟩
    exact pullback_of_primitive_germ H H.continuous ⟨x, hx⟩ (R ⟨x, hx⟩) (hvalue _) a ha

end VeechDichotomy.NativePhysicalDifferentialEquiv
