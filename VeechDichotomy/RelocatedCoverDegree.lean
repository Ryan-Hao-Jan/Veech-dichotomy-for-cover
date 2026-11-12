module

public import VeechDichotomy.RelocatedCoverBranchValues
public import VeechDichotomy.NativeFullCoverDegree

/-! Relocation preserves actual covering fibers and the positive native
degree. The fiber identification is a literal homeomorphism, also over
branch values; constancy of degree is used only off the branch set. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelocatedCoverDegree

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

def fiberHomeomorph (x : X) :
    ((cover π ψ hψ hInv).map ⁻¹' {ψ x}) ≃ₜ (π.map ⁻¹' {x}) :=
  (toOriginal π ψ hψ hInv).subtype
    (p := fun y => y ∈ (cover π ψ hψ hInv).map ⁻¹' {ψ x})
    (q := fun y => y ∈ π.map ⁻¹' {x}) (by
      intro i
      change ψ (π.map i.point) = ψ x ↔ π.map i.point = x
      exact ψ.injective.eq_iff)

theorem fiber_card_eq (x : X) : Nat.card ((cover π ψ hψ hInv).map ⁻¹' {ψ x}) = Nat.card (π.map ⁻¹' {x}) :=
  Nat.card_congr (fiberHomeomorph π ψ hψ hInv x).toEquiv

theorem degree_eq : NativeFullCoverDegree.degree (cover π ψ hψ hInv) = NativeFullCoverDegree.degree π := by
  let x := NativeFullCoverDegree.reference π
  have hnew : ψ x.val ∉ branchValues (cover π ψ hψ hInv) := by
    rw [RelocatedCoverBranchValues.branchValues_eq_image]
    rintro ⟨y, hy, heq⟩
    have hyx : y = x.val := ψ.injective heq
    exact x.property (hyx ▸ hy)
  calc
    NativeFullCoverDegree.degree (cover π ψ hψ hInv) =
        Nat.card ((cover π ψ hψ hInv).map ⁻¹' {ψ x.val}) :=
      (NativeFullCoverDegree.fiber_card_eq_degree _ hnew).symm
    _ = Nat.card (π.map ⁻¹' {x.val}) := fiber_card_eq π ψ hψ hInv x.val
    _ = NativeFullCoverDegree.degree π := NativeFullCoverDegree.fiber_card_eq_degree π x.property

end VeechDichotomy.RelocatedCoverDegree
