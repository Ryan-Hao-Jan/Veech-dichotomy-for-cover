module

public import VeechDichotomy.NativeAffineNormalization
public import VeechDichotomy.NativeDeformationBranchValues
public import VeechDichotomy.NativeCoverEquivalence

/-! The actual cover underlying a normalized marked base representative.
The source remains the time-deformed cover surface; the base is identified
by the proved native normalization equivalence. No lift of the base affine
automorphism to the cover is required or supplied. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeNormalizedCover

open MNEC.NativeAbelianDifferential MNEC.NativeDifferentialEquiv
open NativeVeech NativeTranslationCover NativeDeformationCover NativeDeformationRegular
open WholeDeformedAtlas LinearGroup Set
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

def normalizedCover (π : Cover ωX ωY) {γ : SL2} (φ : AffineAutomorphism ωX γ) (A : SL2) :
    Cover (transformed ωX (A * γ)) (transformed ωY A) :=
  NativeCoverEquivalence.postcompose (cover π A)
    (NativeDifferentialEquivalenceLaws.symm (NativeAffineNormalization.equivalence ωX φ A))

theorem normalization_inverse_value {γ : SL2} (φ : AffineAutomorphism ωX γ) (A : SL2) (x : X) :
    (NativeAffineNormalization.equivalence ωX φ A).homeomorph.symm ((toOriginal ωX A).symm x) =
      (toOriginal ωX (A * γ)).symm (φ.surface.symm x) := rfl

@[simp] theorem normalizedCover_map (π : Cover ωX ωY) {γ : SL2}
    (φ : AffineAutomorphism ωX γ) (A : SL2) (y : Y) :
    (normalizedCover π φ A).map ((toOriginal ωY A).symm y) =
      (toOriginal ωX (A * γ)).symm (φ.surface.symm (π.map y)) := rfl

theorem branchValues_normalizedCover (π : Cover ωX ωY) {γ : SL2}
    (φ : AffineAutomorphism ωX γ) (A : SL2) :
    branchValues (normalizedCover π φ A) =
      ((toOriginal ωX (A * γ)).symm ∘ φ.surface.symm) '' branchValues π := by
  rw [normalizedCover, NativeCoverEquivalence.branchValues_postcompose,
    NativeDeformationBranchValues.branchValues_eq_image, image_image]
  apply image_congr
  intro x _
  exact normalization_inverse_value φ A x

theorem normalized_branch_tuple (π : Cover ωX ωY) {γ : SL2}
    (φ : AffineAutomorphism ωX γ) (A : SL2) {m : ℕ} (b : Fin m → X)
    (hb : range b = branchValues π) :
    range (fun i => (toOriginal ωX (A * γ)).symm (φ.surface.symm (b i))) =
      branchValues (normalizedCover π φ A) := by
  rw [branchValues_normalizedCover, ← hb, ← range_comp]
  rfl

end VeechDichotomy.NativeNormalizedCover
