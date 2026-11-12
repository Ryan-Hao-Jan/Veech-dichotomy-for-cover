module

public import MNEC.NativeRemovableMaps

/-! Completing a genuine regular one-form isomorphism across the actual
finite zero sets. The whole-curve homeomorphism is retained literally;
holomorphicity and the one-form identity at the zeros are derived.
The actual regular differentiability and pullback premises must come
from the computed physical chart germs in geometric applications. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeDifferentialEquivCompletion

open NativeAbelianDifferential NativeRegularTranslationAtlas NativeDifferentialEquiv
open Set
open scoped Manifold ContDiff

set_option autoImplicit false

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {q : Differential X} {r : Differential Y}

theorem regular_iff (H : X ≃ₜ Y) (R : Regular q ≃ₜ Regular r)
    (hvalue : ∀ x : Regular q, (R x).val = H x.val) (x : X) :
    x ∈ regularSet q ↔ H x ∈ regularSet r := by
  constructor
  · intro hx
    have h := (R ⟨x, hx⟩).property
    rwa [hvalue] at h
  · intro hx
    let y : Regular r := ⟨H x, hx⟩
    let z := R.symm y
    have hz : H z.val = H x := by
      rw [← hvalue]
      exact congrArg Subtype.val (R.apply_symm_apply y)
    have hzx : z.val = x := H.injective hz
    exact hzx ▸ z.property

def of_regular (H : X ≃ₜ Y) (R : Regular q ≃ₜ Regular r)
    (hvalue : ∀ x : Regular q, (R x).val = H x.val)
    (hD : ∀ x : X, x ∈ regularSet q → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H x)
    (hInv : ∀ y : Y, y ∈ regularSet r → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H.symm y)
    (hPull : ∀ x : X, x ∈ regularSet q → q.val.toFun x =
      (r.val.toFun (H x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) H x)) : Equiv q r where
  homeomorph := H
  differentiable := NativeRemovableMaps.mdifferentiable_of_continuous_off_finite H
    H.continuous (zeroSet q) (zeroSet_finite q) hD
  inverse_differentiable := NativeRemovableMaps.mdifferentiable_of_continuous_off_finite H.symm
    H.symm.continuous (zeroSet r) (zeroSet_finite r) hInv
  oneForm_pullback x := by
    by_cases hx : x ∈ regularSet q
    · exact hPull x hx
    · have hqzero : q.val.toFun x = 0 := by
        by_contra h
        exact hx h
      have hrzero : r.val.toFun (H x) = 0 := by
        by_contra h
        exact hx ((regular_iff H R hvalue x).mpr h)
      rw [hqzero, hrzero, ContinuousLinearMap.zero_comp]

@[simp] theorem of_regular_homeomorph (H : X ≃ₜ Y) (R : Regular q ≃ₜ Regular r)
    (hvalue : ∀ x : Regular q, (R x).val = H x.val)
    (hD : ∀ x : X, x ∈ regularSet q → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H x)
    (hInv : ∀ y : Y, y ∈ regularSet r → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H.symm y)
    (hPull : ∀ x : X, x ∈ regularSet q → q.val.toFun x =
      (r.val.toFun (H x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) H x)) :
    (of_regular H R hvalue hD hInv hPull).homeomorph = H := rfl

end MNEC.NativeDifferentialEquivCompletion

