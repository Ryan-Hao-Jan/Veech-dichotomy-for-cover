module

public import VeechDichotomy.NativeSurface
public import MNEC.NativeLocalPrimitives
public import Mathlib.Topology.Maps.Proper.Basic

/-! Genuine finite holomorphic translation-cover data between compact
connected curves with nonzero holomorphic differentials.
Branch values are DEFINED by the critical points of the holomorphic map;
their finiteness is proved from the pullback identity, not assumed.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeTranslationCover

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveTransitions
open Set Topology Filter
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

structure Cover (ωX : Differential X) (ωY : Differential Y) where
  map : Y → X
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω map
  surjective : Function.Surjective map
  finite_fibers : ∀ x : X, (map ⁻¹' {x}).Finite
  pullback_eq : Jacobians.pullbackForm map holomorphic ωX.val = ωY.val

variable {ωX : Differential X} {ωY : Differential Y}

def criticalSet (π : Cover ωX ωY) : Set Y :=
  {y | mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y = 0}

def branchValues (π : Cover ωX ωY) : Set X := π.map '' criticalSet π

theorem pullback_at (π : Cover ωX ωY) (y : Y) :
    ωY.val.toFun y = (ωX.val.toFun (π.map y)).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y) :=
  (congrArg (fun α : Jacobians.HolomorphicOneForms Y => α.toFun y) π.pullback_eq).symm

theorem critical_subset_zeroSet (π : Cover ωX ωY) :
    criticalSet π ⊆ zeroSet ωY := by
  intro y hy
  change ωY.val.toFun y = 0
  rw [pullback_at π y, hy]
  exact ContinuousLinearMap.comp_zero _

theorem criticalSet_finite (π : Cover ωX ωY) : (criticalSet π).Finite :=
  (zeroSet_finite ωY).subset (critical_subset_zeroSet π)

theorem branchValues_finite (π : Cover ωX ωY) : (branchValues π).Finite :=
  (criticalSet_finite π).image π.map

theorem branchValues_closed (π : Cover ωX ωY) : IsClosed (branchValues π) :=
  (branchValues_finite π).isClosed

theorem regular_maps_to_regular (π : Cover ωX ωY) {y : Y}
    (hy : y ∈ regularSet ωY) : π.map y ∈ regularSet ωX := by
  intro hx
  apply hy
  change ωY.val.toFun y = 0
  rw [pullback_at π y, hx]
  exact ContinuousLinearMap.zero_comp _

theorem derivative_ne_zero_on_regular (π : Cover ωX ωY) {y : Y}
    (hy : y ∈ regularSet ωY) : mfderiv 𝓘(ℂ) 𝓘(ℂ) π.map y ≠ 0 := by
  intro hc
  exact hy (critical_subset_zeroSet π hc)

def regularMap (π : Cover ωX ωY) : Regular ωY → Regular ωX :=
  fun y => ⟨π.map y.val, regular_maps_to_regular π y.property⟩

theorem continuous_regularMap (π : Cover ωX ωY) : Continuous (regularMap π) :=
  (π.holomorphic.continuous.comp continuous_subtype_val).subtype_mk _

theorem isProperMap (π : Cover ωX ωY) : IsProperMap π.map :=
  π.holomorphic.continuous.isProperMap

/-- A base primitive pulls back to a primitive of the covering form. -/
theorem pullback_primitive_derivative (π : Cover ωX ωY)
    (e : OpenPartialHomeomorph X ℂ)
    (he : ∀ x ∈ e.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) e x (ωX.val.toFun x))
    (y : Y) (hy : π.map y ∈ e.source) :
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (e ∘ π.map) y (ωY.val.toFun y) := by
  rw [pullback_at π y]
  exact (he (π.map y) hy).comp y (π.holomorphic.mdifferentiableAt (by decide)).hasMFDerivAt

/-- The genuine translation-cover formula in ANY two primitive charts
containing the point and its image. Its translation term is derived. -/
theorem local_translation_in_primitive_charts (π : Cover ωX ωY)
    (eX : OpenPartialHomeomorph X ℂ) (eY : OpenPartialHomeomorph Y ℂ)
    (heX : ∀ x ∈ eX.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) eX x (ωX.val.toFun x))
    (heY : ∀ y ∈ eY.source, HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) eY y (ωY.val.toFun y))
    (y : Y) (hy : y ∈ eY.source) (hπy : π.map y ∈ eX.source) :
    ∀ᶠ z in 𝓝 y,
      eX (π.map z) = eY z + (eX (π.map y) - eY y) :=
  MNEC.NativeLocalPrimitives.difference_germ ωY eY (eX ∘ π.map)
    eY.source (π.map ⁻¹' eX.source) eY.open_source
    (eX.open_source.preimage π.holomorphic.continuous) heY
    (fun z hz => pullback_primitive_derivative π eX heX z hz) y ⟨hy, hπy⟩

theorem local_translation (π : Cover ωX ωY) (y : Regular ωY) :
    ∀ᶠ z in 𝓝 y.val,
      (primitiveChart ωX (regularMap π y)) (π.map z) =
        primitiveChart ωY y z +
          (primitiveChart ωX (regularMap π y) (π.map y.val) - primitiveChart ωY y y.val) :=
  local_translation_in_primitive_charts π _ _
    (chosen ωX (regularMap π y)).derivative (chosen ωY y).derivative
    y.val (chosen ωY y).center (chosen ωX (regularMap π y)).center

end VeechDichotomy.NativeTranslationCover
