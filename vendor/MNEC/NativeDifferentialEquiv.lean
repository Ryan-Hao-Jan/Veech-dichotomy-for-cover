module

public import MNEC.NativeRegularTranslationAtlas

/-! Genuine equivalences of native differentials: actual curve
homeomorphisms, complex differentiability in both directions, and the
literal intrinsic pullback equation for the one-forms. Area, native-flow
and coefficient preservation are NOT fields. These are to be derived.
Existence of such an equivalence from an arbitrary q to a slit model
remains the separate geometric realization theorem. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeDifferentialEquiv

open NativeAbelianDifferential NativeRegularTranslationAtlas Set Topology
open scoped Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

structure Equiv (q : Differential X) (r : Differential Y) where
  homeomorph : X ≃ₜ Y
  differentiable : ∀ x : X, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) homeomorph x
  inverse_differentiable : ∀ y : Y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) homeomorph.symm y
  oneForm_pullback : ∀ x : X, q.val.toFun x = (r.val.toFun (homeomorph x)).comp
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) homeomorph x)

variable {q : Differential X} {r : Differential Y}

theorem derivative_inverse_cancel (e : Equiv q r) (y : Y) :
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph (e.homeomorph.symm y)).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph.symm y) = ContinuousLinearMap.id ℂ ℂ := by
  have h := (e.differentiable (e.homeomorph.symm y)).hasMFDerivAt.comp y
    (e.inverse_differentiable y).hasMFDerivAt
  have hId : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) id y
      ((mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph (e.homeomorph.symm y)).comp
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph.symm y)) := by
    apply h.congr_of_eventuallyEq_abuse
    exact Filter.Eventually.of_forall (fun z => (e.homeomorph.apply_symm_apply z).symm)
  have hD := HasMFDerivAt.mfderiv hId
  simpa only [mfderiv_id] using! hD.symm

theorem inverse_oneForm_pullback (e : Equiv q r) (y : Y) :
    r.val.toFun y = (q.val.toFun (e.homeomorph.symm y)).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph.symm y) := by
  let a : ℂ →L[ℂ] ℂ := q.val.toFun (e.homeomorph.symm y)
  let b : ℂ →L[ℂ] ℂ := r.val.toFun (e.homeomorph (e.homeomorph.symm y))
  let d : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph (e.homeomorph.symm y)
  let dinv : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e.homeomorph.symm y
  have hp : a = b.comp d := e.oneForm_pullback (e.homeomorph.symm y)
  have hc : d.comp dinv = ContinuousLinearMap.id ℂ ℂ := derivative_inverse_cancel e y
  have h : a.comp dinv = b := by
    rw [hp, ContinuousLinearMap.comp_assoc, hc, ContinuousLinearMap.comp_id]
  have hb : b = r.val.toFun y := by
    apply ContinuousLinearMap.ext
    intro v
    change (fun z : Y => (r.val.toFun z v : ℂ)) (e.homeomorph (e.homeomorph.symm y)) =
      (fun z : Y => (r.val.toFun z v : ℂ)) y
    exact congrArg (fun z : Y => (r.val.toFun z v : ℂ)) (e.homeomorph.apply_symm_apply y)
  exact hb.symm.trans h.symm

theorem maps_regular (e : Equiv q r) (x : X) (hx : x ∈ regularSet q) :
    e.homeomorph x ∈ regularSet r := by
  change q.val.toFun x ≠ 0 at hx
  change r.val.toFun (e.homeomorph x) ≠ 0
  intro hzero
  apply hx
  rw [e.oneForm_pullback, hzero, ContinuousLinearMap.zero_comp]

theorem inverse_maps_regular (e : Equiv q r) (y : Y) (hy : y ∈ regularSet r) :
    e.homeomorph.symm y ∈ regularSet q := by
  change r.val.toFun y ≠ 0 at hy
  change q.val.toFun (e.homeomorph.symm y) ≠ 0
  intro hzero
  apply hy
  rw [inverse_oneForm_pullback e y, hzero, ContinuousLinearMap.zero_comp]

def regularHomeomorph (e : Equiv q r) : Regular q ≃ₜ Regular r where
  toFun x := ⟨e.homeomorph x.val, maps_regular e x.val x.property⟩
  invFun y := ⟨e.homeomorph.symm y.val, inverse_maps_regular e y.val y.property⟩
  left_inv x := Subtype.ext (e.homeomorph.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.homeomorph.apply_symm_apply y.val)
  continuous_toFun := (e.homeomorph.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.homeomorph.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem regularHomeomorph_value (e : Equiv q r) (x : Regular q) :
    (regularHomeomorph e x).val = e.homeomorph x.val := rfl

@[simp] theorem regularHomeomorph_symm_value (e : Equiv q r) (y : Regular r) :
    ((regularHomeomorph e).symm y).val = e.homeomorph.symm y.val := rfl

/-- Pulling a CONSTRUCTED target primitive through the actual curve
equivalence constructs a source primitive with the source intrinsic q. -/
def pulledPrimitive (e : Equiv q r) (x : Regular q) : NativePrimitiveTransitions.PrimitiveChart q x := by
  let P := NativePrimitiveTransitions.chosen r (regularHomeomorph e x)
  refine ⟨e.homeomorph.toOpenPartialHomeomorph.trans P.chart, ⟨mem_univ _, P.center⟩, ?_, ?_⟩
  · intro y hy
    have hreg := inverse_maps_regular e (e.homeomorph y) (P.regular_source hy.2)
    simpa only [Homeomorph.symm_apply_apply] using hreg
  · intro y hy
    have h := (P.derivative (e.homeomorph y) hy.2).comp y (e.differentiable y).hasMFDerivAt
    change HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (fun z => P.chart (e.homeomorph z)) y (q.val.toFun y)
    rw [e.oneForm_pullback]
    exact h

end MNEC.NativeDifferentialEquiv

