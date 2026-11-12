module

public import VeechDichotomy.NativeNormalizedCoverSequences

/-! Compact returns of actual base quotient classes give an actual
native analytic-family limit of the original deformed covering sources.
All normalizing base affine maps are derived from compact quotient
lifting; an affine lift to the covering source is not assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeNormalizedCoverCompactness

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup NativeVeech
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y}

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qX B) := WholeDeformedAtlas.chartedSpace qX B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qX B) := WholeDeformedAtlas.isComplexManifold qX B ω
local instance (B : SL2) : ChartedSpace ℂ (WholeSurface qY B) := WholeDeformedAtlas.chartedSpace qY B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface qY B) := WholeDeformedAtlas.isComplexManifold qY B ω

theorem from_quotient_sequence (π : Cover qX qY) {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π)
    {C : Set (Fin m → X)} (hC : IsCompact C) (hCi : invariant (NativeAffineGroup.AffineGroup qX) C)
    (hbC : b ∈ C) (hconf : C ⊆ configuration m X)
    (a : ℕ → SL2) {D : Set (SL2 ⧸ derivativeGroup qX)} (hD : IsCompact D)
    (hreturn : ∀ n, (QuotientGroup.mk (a n) : SL2 ⧸ derivativeGroup qX) ∈ D) :
    ∃ K : Set SL2, IsCompact K ∧ ∃ γ : ℕ → SL2, ∃ φ : ∀ n, AffineAutomorphism qX (γ n),
      (∀ n, NativeNormalizedCoverSequences.matrix a γ n ∈ K) ∧
      (∀ n, NativeNormalizedCoverSequences.branches b φ n ∈ C) ∧
      NativeCoverFamilyLimits.FamilyLimit (fun n => WholeSurface qY (a n))
        (NativeNormalizedCoverSequences.matrix a γ) (NativeNormalizedCoverSequences.branches b φ)
        (fun n => transformed qY (a n)) (NativeNormalizedCoverSequences.cover π a γ φ)
        (NativeNormalizedCoverSequences.branch_tuple π a γ φ b hb) K C := by
  classical
  obtain ⟨K, hK, _, hnorm⟩ := NativeCompactNormalizedCovers.compact_normalized_parameters π b hb hC hCi hbC hD
  choose γ φ hprops using fun n => hnorm (a n) (hreturn n)
  have hmat : ∀ n, NativeNormalizedCoverSequences.matrix a γ n ∈ K := fun n => (hprops n).1.1
  have hmarks : ∀ n, NativeNormalizedCoverSequences.branches b φ n ∈ C := fun n => (hprops n).1.2
  exact ⟨K, hK, γ, φ, hmat, hmarks,
    NativeNormalizedCoverSequences.compact_family_limit π a γ φ b hb hK hmat hC hmarks hconf⟩

end VeechDichotomy.NativeNormalizedCoverCompactness
