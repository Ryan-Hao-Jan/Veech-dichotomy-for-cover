module

public import VeechDichotomy.NativePhysicalHolomorphicMap
public import VeechDichotomy.NativeDeformationRegular
public import VeechDichotomy.NativeCoverFlow

/-! Simultaneous SL2 deformation of a genuine finite translation cover.
The actual map is transported through the constructed surface homeomorphisms;
its holomorphicity and form pullback are proved, including ramification. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDeformationCover

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover NativeDeformationRegular NativeVeech
open LinearGroup LinearEquivalences WholeDeformedAtlas Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

local instance (q : Differential X) (A : SL2) : ChartedSpace ℂ (WholeSurface q A) :=
  WholeDeformedAtlas.chartedSpace q A
local instance (q : Differential X) (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) :=
  WholeDeformedAtlas.isComplexManifold q A ω
local instance (q : Differential Y) (A : SL2) : ChartedSpace ℂ (WholeSurface q A) :=
  WholeDeformedAtlas.chartedSpace q A
local instance (q : Differential Y) (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q A) :=
  WholeDeformedAtlas.isComplexManifold q A ω
local instance : ChartedSpace Plane (Regular ωX) := MNEC.NativeRegularTranslationAtlas.chartedSpace ωX
local instance : ChartedSpace Plane (Regular ωY) := MNEC.NativeRegularTranslationAtlas.chartedSpace ωY
local instance (A : SL2) : ChartedSpace Plane (Regular (transformed ωX A)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed ωX A)
local instance (A : SL2) : ChartedSpace Plane (Regular (transformed ωY A)) :=
  MNEC.NativeRegularTranslationAtlas.chartedSpace (transformed ωY A)

def map (π : Cover ωX ωY) (A : SL2) : WholeSurface ωY A → WholeSurface ωX A :=
  fun y => (toOriginal ωX A).symm (π.map (toOriginal ωY A y))

theorem continuous_map (π : Cover ωX ωY) (A : SL2) : Continuous (map π A) :=
  (toOriginal ωX A).symm.continuous.comp (π.holomorphic.continuous.comp (toOriginal ωY A).continuous)

def regularMap (π : Cover ωX ωY) (A : SL2) : Regular (transformed ωY A) → Regular (transformed ωX A) :=
  fun y => regularHomeomorph ωX A (NativeTranslationCover.regularMap π ((regularHomeomorph ωY A).symm y))

theorem continuous_regularMap (π : Cover ωX ωY) (A : SL2) : Continuous (regularMap π A) :=
  (regularHomeomorph ωX A).continuous.comp
    ((NativeTranslationCover.continuous_regularMap π).comp (regularHomeomorph ωY A).symm.continuous)

theorem regularMap_value (π : Cover ωX ωY) (A : SL2) (y : Regular (transformed ωY A)) :
    (regularMap π A y).val = map π A y.val := rfl

theorem regularMap_derivative (π : Cover ωX ωY) (A : SL2) (y : Regular (transformed ωY A)) :
    HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (regularMap π A) y
      (ContinuousLinearMap.id ℝ Plane) := by
  have hY := hasMFDerivAt_regularHomeomorph_symm ωY A y
  have hπ := NativeCoverFlow.hasMFDerivAt_regularMap π ((regularHomeomorph ωY A).symm y)
  have hX := hasMFDerivAt_regularHomeomorph ωX A
    (NativeTranslationCover.regularMap π ((regularHomeomorph ωY A).symm y))
  have hcomp := hX.comp y (hπ.comp y hY)
  have hlin : (planeEquiv A).toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ Plane).comp (planeEquiv A).symm.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ Plane := by
    rw [ContinuousLinearMap.id_comp]
    change (linear A).comp (linear A⁻¹) = _
    rw [← linear_mul, mul_inv_cancel, linear_one]
  rw [hlin] at hcomp
  exact hcomp

theorem holomorphic_map (π : Cover ωX ωY) (A : SL2) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (map π A) :=
  NativePhysicalHolomorphicMap.holomorphic (map π A) (continuous_map π A)
    (regularMap π A) (continuous_regularMap π A) (regularMap_value π A) (regularMap_derivative π A)

def cover (π : Cover ωX ωY) (A : SL2) : Cover (transformed ωX A) (transformed ωY A) where
  map := map π A
  holomorphic := holomorphic_map π A
  surjective x := by
    obtain ⟨y, hy⟩ := π.surjective (toOriginal ωX A x)
    refine ⟨(toOriginal ωY A).symm y, ?_⟩
    change (toOriginal ωX A).symm (π.map (toOriginal ωY A ((toOriginal ωY A).symm y))) = x
    rw [Homeomorph.apply_symm_apply, hy, Homeomorph.symm_apply_apply]
  finite_fibers x := by
    apply ((π.finite_fibers (toOriginal ωX A x)).image (toOriginal ωY A).symm).subset
    intro y hy
    refine ⟨toOriginal ωY A y, ?_, (toOriginal ωY A).symm_apply_apply y⟩
    change π.map (toOriginal ωY A y) = toOriginal ωX A x
    have h := congrArg (toOriginal ωX A) hy
    change toOriginal ωX A ((toOriginal ωX A).symm (π.map (toOriginal ωY A y))) = toOriginal ωX A x at h
    simpa only [Homeomorph.apply_symm_apply] using h
  pullback_eq := NativePhysicalHolomorphicMap.pullback_eq (map π A) (holomorphic_map π A)
    (regularMap π A) (continuous_regularMap π A) (regularMap_value π A) (regularMap_derivative π A)

@[simp] theorem cover_map_value (π : Cover ωX ωY) (A : SL2) (y : Y) :
    (cover π A).map ((toOriginal ωY A).symm y) = (toOriginal ωX A).symm (π.map y) := rfl

end VeechDichotomy.NativeDeformationCover
