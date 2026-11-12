module

public import VeechDichotomy.NativePuncturedCoverClassification
public import VeechDichotomy.FinitePunctureHomeomorphExtension
public import VeechDichotomy.NativeCoverIsomorphism
public import VeechDichotomy.NumberedCoverMonodromy

/-! Classification of whole native finite translation covers by actual
monodromy: an equivariant fiber bijection yields a genuine whole-curve
holomorphic differential equivalence commuting with the cover maps.
Extension across all finite branch fibers is proved, not assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverMonodromyClassification

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeRelativePuncturedCover
open FinitePunctureNeighborhoods Set Topology
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

theorem extend_isomorphism (π : Cover ωX ωY) (ρ : Cover ωX ωZ) {B : Set X}
    (hB : B.Finite) (h : source π B ≃ₜ source ρ B)
    (hsquare : ∀ y, ρ.map (h y).val = π.map y.val) :
    ∃ e : MNEC.NativeDifferentialEquiv.Equiv ωY ωZ,
      (∀ y : source π B, e.homeomorph y.val = (h y).val) ∧
      ∀ y, ρ.map (e.homeomorph y) = π.map y := by
  obtain ⟨H, hH, hcomm⟩ := FinitePunctureHomeomorphExtension.exists_extension
    (preimage_finite π hB) (preimage_finite ρ hB)
    π.map π.holomorphic.continuous π.finite_fibers
    ρ.map ρ.holomorphic.continuous ρ.finite_fibers h hsquare
  have hs : ∀ y, ρ.map (H y) = π.map y := congrFun hcomm
  exact ⟨NativeCoverIsomorphism.equivalence_of_commutes π ρ H hs, hH, hs⟩

theorem exists_equivalence (π : Cover ωX ωY) (ρ : Cover ωX ωZ) {B : Set X}
    (hB : B.Finite) (hπ : branchValues π ⊆ B) (hρ : branchValues ρ ⊆ B)
    (x : base B) (h : (map π B ⁻¹' {x}) ≃ (map ρ B ⁻¹' {x}))
    (hh : CoverMonodromyClassification.Equivariant (isCoveringMap π hπ) (isCoveringMap ρ hρ) h) :
    ∃ e : MNEC.NativeDifferentialEquiv.Equiv ωY ωZ, ∀ y, ρ.map (e.homeomorph y) = π.map y := by
  obtain ⟨H, hH⟩ := NativePuncturedCoverClassification.exists_isomorphism π ρ hB hπ hρ x h hh
  obtain ⟨e, _, he⟩ := extend_isomorphism π ρ hB H hH
  exact ⟨e, he⟩

theorem exists_equivalence_of_numbered_eq (π : Cover ωX ωY) (ρ : Cover ωX ωZ)
    {B : Set X} (hB : B.Finite) (hπ : branchValues π ⊆ B) (hρ : branchValues ρ ⊆ B)
    (x : base B) {d : ℕ} (α : (map π B ⁻¹' {x}) ≃ Fin d) (β : (map ρ B ⁻¹' {x}) ≃ Fin d)
    (heq : NumberedCoverMonodromy.representation (isCoveringMap π hπ) α =
      NumberedCoverMonodromy.representation (isCoveringMap ρ hρ) β) :
    ∃ e : MNEC.NativeDifferentialEquiv.Equiv ωY ωZ, ∀ y, ρ.map (e.homeomorph y) = π.map y :=
  exists_equivalence π ρ hB hπ hρ x (α.trans β.symm)
    (NumberedCoverMonodromy.equivariant_of_eq (isCoveringMap π hπ) (isCoveringMap ρ hρ) α β heq)

end VeechDichotomy.NativeCoverMonodromyClassification
