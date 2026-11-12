module

public import VeechDichotomy.RelocatedCoverBranchValues

/-! Relocating the base of two actually equivalent native covers
preserves their equivalence. The new whole homeomorphism is explicit;
holomorphicity and form preservation follow from the commuting native
cover maps, not from global holomorphicity of the base transport. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverEquivalence

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverAtlas
open Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {ωX : Differential X} {ωY : Differential Y} {ωZ : Differential Z}
variable (π : Cover ωX ωY) (ρ : Cover ωX ωZ) (ψ : X ≃ₜ X)
variable (hπ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hπInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)
variable (hρ : ∀ b ∈ branchValues ρ, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hρInv : ∀ b ∈ branchValues ρ, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)

def sourceHomeomorph (e : MNEC.NativeDifferentialEquiv.Equiv ωY ωZ) :
    Surface π ψ hπ hπInv ≃ₜ Surface ρ ψ hρ hρInv :=
  ((toOriginal π ψ hπ hπInv).trans e.homeomorph).trans (toOriginal ρ ψ hρ hρInv).symm

def equivalence (e : MNEC.NativeDifferentialEquiv.Equiv ωY ωZ)
    (he : ∀ y, ρ.map (e.homeomorph y) = π.map y) :
    MNEC.NativeDifferentialEquiv.Equiv (RelocatedCoverDifferential.form π ψ hπ hπInv)
      (RelocatedCoverDifferential.form ρ ψ hρ hρInv) :=
  NativeCoverIsomorphism.equivalence_of_commutes
    (RelocatedCoverDifferential.cover π ψ hπ hπInv) (RelocatedCoverDifferential.cover ρ ψ hρ hρInv)
    (sourceHomeomorph π ρ ψ hπ hπInv hρ hρInv e) (by
      intro i
      change ψ (ρ.map (e.homeomorph i.point)) = ψ (π.map i.point)
      exact congrArg ψ (he i.point))

theorem commutes (e : MNEC.NativeDifferentialEquiv.Equiv ωY ωZ)
    (he : ∀ y, ρ.map (e.homeomorph y) = π.map y) (i : Surface π ψ hπ hπInv) :
    (RelocatedCoverDifferential.cover ρ ψ hρ hρInv).map
      ((equivalence π ρ ψ hπ hπInv hρ hρInv e he).homeomorph i) =
        (RelocatedCoverDifferential.cover π ψ hπ hπInv).map i := by
  change ψ (ρ.map (e.homeomorph i.point)) = ψ (π.map i.point)
  exact congrArg ψ (he i.point)

end VeechDichotomy.RelocatedCoverEquivalence
