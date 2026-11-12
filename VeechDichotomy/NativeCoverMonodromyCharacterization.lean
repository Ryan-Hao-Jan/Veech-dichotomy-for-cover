module

public import VeechDichotomy.NativeCoverMonodromyClassification
public import VeechDichotomy.CoverMonodromyNaturality

/-! Two genuine native translation covers of the same pointed base are
equivalent exactly when their actual monodromy fibers are equivariantly
bijective. This includes extension over ramification and form preservation.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverMonodromyCharacterization

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeRelativePuncturedCover
open Set
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

def restrictHomeomorph (π : Cover ωX ωY) (ρ : Cover ωX ωZ) (H : Y ≃ₜ Z)
    (hsquare : ∀ y, ρ.map (H y) = π.map y) (B : Set X) : source π B ≃ₜ source ρ B :=
  H.subtype (p := fun y => y ∈ source π B) (q := fun z => z ∈ source ρ B) (by
    intro y
    change π.map y ∉ B ↔ ρ.map (H y) ∉ B
    rw [hsquare])

theorem restrictHomeomorph_commutes (π : Cover ωX ωY) (ρ : Cover ωX ωZ) (H : Y ≃ₜ Z)
    (hsquare : ∀ y, ρ.map (H y) = π.map y) (B : Set X) :
    map ρ B ∘ restrictHomeomorph π ρ H hsquare B = map π B := by
  funext y
  apply Subtype.ext
  exact hsquare y.val

theorem exists_equivalence_iff (π : Cover ωX ωY) (ρ : Cover ωX ωZ) {B : Set X}
    (hB : B.Finite) (hπ : branchValues π ⊆ B) (hρ : branchValues ρ ⊆ B) (x : base B) :
    (∃ e : MNEC.NativeDifferentialEquiv.Equiv ωY ωZ, ∀ y, ρ.map (e.homeomorph y) = π.map y) ↔
      ∃ h : (map π B ⁻¹' {x}) ≃ (map ρ B ⁻¹' {x}),
        CoverMonodromyClassification.Equivariant (isCoveringMap π hπ) (isCoveringMap ρ hρ) h := by
  constructor
  · rintro ⟨e, he⟩
    let H := restrictHomeomorph π ρ e.homeomorph he B
    have hH := restrictHomeomorph_commutes π ρ e.homeomorph he B
    exact ⟨CoverMonodromyNaturality.fiberEquiv H hH,
      CoverMonodromyNaturality.equivariant (isCoveringMap π hπ) (isCoveringMap ρ hρ)
        ⟨H, H.continuous⟩ hH⟩
  · rintro ⟨h, hh⟩
    exact NativeCoverMonodromyClassification.exists_equivalence π ρ hB hπ hρ x h hh

end VeechDichotomy.NativeCoverMonodromyCharacterization
