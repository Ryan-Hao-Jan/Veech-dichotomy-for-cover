module

public import VeechDichotomy.NativeCoverFamilyFiniteness
public import VeechDichotomy.NativePuncturedFundamentalGroup

/-! Finiteness of actual native cover classes over a fixed pointed base
and fixed degree, with the fundamental-group finite-generation obligation
discharged. Local Hurwitz charts and properness remain separate results.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeHurwitzFiberFiniteness

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeRelativePuncturedCover
open NativeCoverFamilyFiniteness Set
open scoped Manifold ContDiff

variable {X ι : Type*} (Y : ι → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {ωX : Differential X} (ωY : ∀ i, Differential (Y i)) (π : ∀ i, Cover ωX (ωY i))

theorem finite_classes {B : Set X} (hB : B.Finite) (hbranch : ∀ i, branchValues (π i) ⊆ B)
    (x : base B) {d : ℕ} (hcard : ∀ i, Nat.card (map (π i) B ⁻¹' {x}) = d) :
    Finite (Quotient (coverSetoid Y ωY π)) :=
  NativeCoverFamilyFiniteness.finite_classes Y ωY π hB hbranch x hcard
    (NativePuncturedFundamentalGroup.fundamentalGroup_fg hB x)

end VeechDichotomy.NativeHurwitzFiberFiniteness
