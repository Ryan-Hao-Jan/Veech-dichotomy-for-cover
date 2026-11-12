module

public import VeechDichotomy.NativeScaledBeltramiCover
public import VeechDichotomy.NativeSL2AnalyticFamily
public import VeechDichotomy.NativeDeformationCover

/-! The original native SL2 cover diagrams commute literally with their
analytic-family realizations. Source and base comparisons preserve actual
differentials; no affine lift to the covering source is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeSL2CoverFamilyNaturality

open MNEC.NativeAbelianDifferential NativeTranslationCover LinearGroup Set
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

local instance (A : SL2) : ChartedSpace ℂ (WholeDeformedAtlas.WholeSurface ωX A) := WholeDeformedAtlas.chartedSpace ωX A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeDeformedAtlas.WholeSurface ωX A) := WholeDeformedAtlas.isComplexManifold ωX A ω
local instance (A : SL2) : ChartedSpace ℂ (WholeDeformedAtlas.WholeSurface ωY A) := WholeDeformedAtlas.chartedSpace ωY A
local instance (A : SL2) : IsManifold 𝓘(ℂ) ω (WholeDeformedAtlas.WholeSurface ωY A) := WholeDeformedAtlas.isComplexManifold ωY A ω

theorem native_cover_square (π : Cover ωX ωY) (A : SL2) (y : WholeDeformedAtlas.WholeSurface ωY A) :
    (NativeSL2AnalyticFamily.equivalence ωX A).homeomorph ((NativeDeformationCover.cover π A).map y) =
      (NativeScaledBeltramiCover.cover π (NativeSL2AnalyticFamily.parameters A)).map
        ((NativeSL2AnalyticFamily.equivalence ωY A).homeomorph y) := rfl

theorem total_cover_square (π : Cover ωX ωY) (A : SL2) (y : WholeDeformedAtlas.WholeSurface ωY A) :
    NativeScaledBeltramiCover.map π (NativeSL2AnalyticFamily.embedding ωY A y) =
      NativeSL2AnalyticFamily.embedding ωX A ((NativeDeformationCover.cover π A).map y) := rfl

end VeechDichotomy.NativeSL2CoverFamilyNaturality
