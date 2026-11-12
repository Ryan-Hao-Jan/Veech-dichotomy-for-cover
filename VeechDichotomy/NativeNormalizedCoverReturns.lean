module

public import VeechDichotomy.NativeNormalizedCoverCompactness
public import VeechDichotomy.CompactReturnSequences

/-! Actual normalized cover-source analytic-family limits at arbitrarily
late quotient return times. The source is the original native deformed
covering curve at those times, even though the base matrix is corrected. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeNormalizedCoverReturns

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

theorem from_returns (π : Cover qX qY) {m : ℕ} (b : Fin m → X) (hb : range b = branchValues π)
    {C : Set (Fin m → X)} (hC : IsCompact C) (hCi : invariant (NativeAffineGroup.AffineGroup qX) C)
    (hbC : b ∈ C) (hconf : C ⊆ configuration m X) (a : ℝ → SL2)
    (hreturns : HasCompactReturns (fun t => (QuotientGroup.mk (a t) : SL2 ⧸ derivativeGroup qX))) :
    ∃ t : ℕ → ℝ, StrictMono t ∧ Tendsto t atTop atTop ∧
      ∃ K : Set SL2, IsCompact K ∧ ∃ γ : ℕ → SL2, ∃ φ : ∀ n, AffineAutomorphism qX (γ n),
        (∀ n, NativeNormalizedCoverSequences.matrix (a ∘ t) γ n ∈ K) ∧
        (∀ n, NativeNormalizedCoverSequences.branches b φ n ∈ C) ∧
        NativeCoverFamilyLimits.FamilyLimit (fun n => WholeSurface qY (a (t n)))
          (NativeNormalizedCoverSequences.matrix (a ∘ t) γ) (NativeNormalizedCoverSequences.branches b φ)
          (fun n => transformed qY (a (t n))) (NativeNormalizedCoverSequences.cover π (a ∘ t) γ φ)
          (NativeNormalizedCoverSequences.branch_tuple π (a ∘ t) γ φ b hb) K C := by
  obtain ⟨D, hD, t, ht, htlim, hmem⟩ := hreturns.sequence
  obtain ⟨K, hK, γ, φ, hmat, hmarks, hlimit⟩ :=
    NativeNormalizedCoverCompactness.from_quotient_sequence π b hb hC hCi hbC hconf (a ∘ t) hD hmem
  exact ⟨t, ht, htlim, K, hK, γ, φ, hmat, hmarks, hlimit⟩

end VeechDichotomy.NativeNormalizedCoverReturns
