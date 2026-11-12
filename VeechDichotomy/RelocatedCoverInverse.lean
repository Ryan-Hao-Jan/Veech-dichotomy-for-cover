module

public import VeechDichotomy.RelocatedCoverBranchValues

/-! Inverse base relocation recovers the original actual native cover
up to a computed holomorphic differential equivalence commuting with its
covering map. The double source wrapper is literally unwrapped. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverInverse

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverAtlas
open RelocatedCoverDifferential Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY) (ψ : X ≃ₜ X)
variable (hψ : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ x)
variable (hInv : ∀ b ∈ branchValues π, ∀ᶠ x in 𝓝 (ψ b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x)

include hψ hInv

theorem inverse_forward_near : ∀ b ∈ branchValues (cover π ψ hψ hInv),
    ∀ᶠ x in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm x := by
  intro b hb
  rw [RelocatedCoverBranchValues.branchValues_eq_image] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact hInv a ha

theorem inverse_inverse_near : ∀ b ∈ branchValues (cover π ψ hψ hInv),
    ∀ᶠ x in 𝓝 (ψ.symm b), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ.symm.symm x := by
  intro b hb
  rw [RelocatedCoverBranchValues.branchValues_eq_image] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  simpa only [Homeomorph.symm_apply_apply, Homeomorph.symm_symm] using hψ a ha

abbrev roundTripCover := cover (cover π ψ hψ hInv) ψ.symm
  (inverse_forward_near π ψ hψ hInv) (inverse_inverse_near π ψ hψ hInv)

def sourceHomeomorph :
    Surface (cover π ψ hψ hInv) ψ.symm (inverse_forward_near π ψ hψ hInv)
      (inverse_inverse_near π ψ hψ hInv) ≃ₜ Y :=
  (toOriginal (cover π ψ hψ hInv) ψ.symm (inverse_forward_near π ψ hψ hInv)
    (inverse_inverse_near π ψ hψ hInv)).trans (toOriginal π ψ hψ hInv)

def equivalence : MNEC.NativeDifferentialEquiv.Equiv
    (form (cover π ψ hψ hInv) ψ.symm (inverse_forward_near π ψ hψ hInv)
      (inverse_inverse_near π ψ hψ hInv)) ωY :=
  NativeCoverIsomorphism.equivalence_of_commutes (roundTripCover π ψ hψ hInv) π
    (sourceHomeomorph π ψ hψ hInv) (by
      intro i
      change π.map i.point.point = ψ.symm (ψ (π.map i.point.point))
      exact (ψ.symm_apply_apply _).symm)

theorem commutes (i) : π.map ((equivalence π ψ hψ hInv).homeomorph i) =
    (roundTripCover π ψ hψ hInv).map i := by
  change π.map i.point.point = ψ.symm (ψ (π.map i.point.point))
  exact (ψ.symm_apply_apply _).symm

end VeechDichotomy.RelocatedCoverInverse
