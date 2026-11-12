module

public import VeechDichotomy.NativeRelativePuncturedCover

/-! Actual isomorphisms of punctured native covers are constructed from
equivariant bijections of their actual monodromy fibers over a common
finite marked base. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePuncturedCoverClassification

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeRelativePuncturedCover
open Set Topology
open scoped Manifold ContDiff

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {ωX : Differential X} {ωY : Differential Y} {ωZ : Differential Z}

theorem exists_isomorphism (π : Cover ωX ωY) (ρ : Cover ωX ωZ) {B : Set X}
    (hB : B.Finite) (hπ : branchValues π ⊆ B) (hρ : branchValues ρ ⊆ B)
    (x : base B) (h : (map π B ⁻¹' {x}) ≃ (map ρ B ⁻¹' {x}))
    (hh : CoverMonodromyClassification.Equivariant (isCoveringMap π hπ) (isCoveringMap ρ hρ) h) :
    ∃ H : source π B ≃ₜ source ρ B, ∀ y, ρ.map (H y).val = π.map y.val := by
  let : PathConnectedSpace (source π B) := source_pathConnected π hB
  let : PathConnectedSpace (source ρ B) := source_pathConnected ρ hB
  let : LocallyPathConnectedSpace (source π B) := source_locallyPathConnected π hB
  let : LocallyPathConnectedSpace (source ρ B) := source_locallyPathConnected ρ hB
  obtain ⟨y, hy⟩ := π.surjective x.val
  have hyS : y ∈ source π B := by
    change π.map y ∈ base B
    rw [hy]
    exact x.property
  let a : map π B ⁻¹' {x} := ⟨⟨y, hyS⟩, Subtype.ext hy⟩
  obtain ⟨H, hH, _⟩ := CoverMonodromyClassification.exists_homeomorph
    (isCoveringMap π hπ) (isCoveringMap ρ hρ) h hh a
  refine ⟨H, ?_⟩
  intro z
  exact congrArg Subtype.val (congrFun hH z)

end VeechDichotomy.NativePuncturedCoverClassification
