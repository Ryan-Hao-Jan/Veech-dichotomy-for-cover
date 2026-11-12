module

public import VeechDichotomy.NativeNormalizedCover
public import VeechDichotomy.NativeAffineGroup

/-! Compact matrix and configuration parameters for actual normalized
native covers above a compact derivative-group quotient set. Compactness
in an ambient Hurwitz space is a separate theorem, not asserted here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCompactNormalizedCovers

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeNormalizedCover
open NativeVeech NativeDeformationRegular WholeDeformedAtlas LinearGroup Set Topology
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

theorem compact_normalized_parameters (π : Cover ωX ωY) {m : ℕ} (b : Fin m → X)
    (hb : range b = branchValues π) {F : Set (Fin m → X)} (hF : IsCompact F)
    (hFi : invariant (NativeAffineGroup.AffineGroup ωX) F) (hbF : b ∈ F)
    {C : Set (SL2 ⧸ derivativeGroup ωX)} (hC : IsCompact C) :
    ∃ K : Set SL2, IsCompact K ∧ IsCompact (K ×ˢ F) ∧
      ∀ A : SL2, (QuotientGroup.mk A : SL2 ⧸ derivativeGroup ωX) ∈ C →
        ∃ (γ : SL2) (φ : AffineAutomorphism ωX γ),
          (A * γ, fun i => φ.surface.symm (b i)) ∈ K ×ˢ F ∧
          range (fun i => (toOriginal ωX (A * γ)).symm (φ.surface.symm (b i))) =
            branchValues (normalizedCover π φ A) := by
  obtain ⟨K, hK, hnorm⟩ := exists_compact_right_normalizers (derivativeGroup ωX) hC
  refine ⟨K, hK, hK.prod hF, ?_⟩
  intro A hA
  obtain ⟨γ, hγ⟩ := hnorm A hA
  obtain ⟨φ⟩ := γ.property
  let a : NativeAffineGroup.AffineGroup ωX := ⟨NativeAffineGroup.asRaw φ, γ.val, φ, rfl⟩
  have hmarks : (fun i => φ.surface.symm (b i)) ∈ F := by
    have h := hFi a⁻¹ hbF
    exact h
  exact ⟨γ.val, φ, ⟨hγ, hmarks⟩, normalized_branch_tuple π φ A b hb⟩

end VeechDichotomy.NativeCompactNormalizedCovers
