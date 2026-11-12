module

public import VeechDichotomy.VaryingNativeCoverPullback
public import VeechDichotomy.NativeHurwitzFiberFiniteness
public import VeechDichotomy.FiniteClassRepresentatives

/-! The actual normalized covers of a varying-base family lie over
ONE fixed pointed native base, so the proved monodromy finiteness theorem
supplies finitely many genuine native cover representatives. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.VaryingNativeCoverFiniteness

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiPlane
open Set Filter Topology UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} (Y : ι → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {q : Differential X} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (A : Data q b μ₀) (F : Family A) (L : ι → SL2) (u : ι → Fin m → X)
  (hvalid : ∀ i, Valid A (SL2BeltramiParameters.parameter (L i)) (u i)) (r : ∀ i, Differential (Y i))

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (ρ : ∀ i, Cover (transformed q (L i)) (r i))
  (hbranch : ∀ i, branchValues (ρ i) = range (fun k => (toOriginal q (L i)).symm (u i k)))

abbrev Source (i : ι) := VaryingNativeCoverPullback.NormalizedSource A F (L i) (u i) (hvalid i) (ρ i) (hbranch i)
abbrev differential (i : ι) := VaryingNativeCoverPullback.normalizedDifferential A F (L i) (u i) (hvalid i) (ρ i) (hbranch i)
abbrev cover (i : ι) := VaryingNativeCoverPullback.normalizedCover A F (L i) (u i) (hvalid i) (ρ i) (hbranch i)

theorem branch_values (i : ι) : branchValues (cover Y A F L u hvalid r ρ hbranch i) = range b :=
  VaryingNativeCoverPullback.normalized_branch A F (L i) (u i) (hvalid i) (ρ i) (hbranch i)

theorem degree_eq (i : ι) : NativeFullCoverDegree.degree (cover Y A F L u hvalid r ρ hbranch i) = NativeFullCoverDegree.degree (ρ i) :=
  VaryingNativeCoverPullback.normalized_degree A F (L i) (u i) (hvalid i) (ρ i) (hbranch i)

theorem finite_classes {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (ρ i) = d) :
    Finite (Quotient (NativeCoverFamilyFiniteness.coverSetoid (Source Y A F L u hvalid r ρ hbranch)
      (differential Y A F L u hvalid r ρ hbranch) (cover Y A F L u hvalid r ρ hbranch))) := by
  let : Infinite X := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x, hx⟩ := (finite_range b).exists_notMem
  apply NativeHurwitzFiberFiniteness.finite_classes (Source Y A F L u hvalid r ρ hbranch)
    (differential Y A F L u hvalid r ρ hbranch) (cover Y A F L u hvalid r ρ hbranch)
    (finite_range b) (fun i => (branch_values Y A F L u hvalid r ρ hbranch i).subset) ⟨x, hx⟩
  intro i
  calc
    Nat.card (NativeRelativePuncturedCover.map (cover Y A F L u hvalid r ρ hbranch i) (range b) ⁻¹' {⟨x, hx⟩}) =
        Nat.card ((cover Y A F L u hvalid r ρ hbranch i).map ⁻¹' {x}) :=
      Nat.card_congr (NativeRelativePuncturedCover.fiberEquiv _ _ _)
    _ = NativeFullCoverDegree.degree (cover Y A F L u hvalid r ρ hbranch i) :=
      NativeFullCoverDegree.fiber_card_eq_degree _ (by rw [branch_values]; exact hx)
    _ = NativeFullCoverDegree.degree (ρ i) := degree_eq Y A F L u hvalid r ρ hbranch i
    _ = d := hdegree i

theorem finite_representatives {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (ρ i) = d) :
    ∃ J : Set ι, J.Finite ∧ ∀ i, ∃ j ∈ J,
      ∃ e : MNEC.NativeDifferentialEquiv.Equiv (differential Y A F L u hvalid r ρ hbranch i)
        (differential Y A F L u hvalid r ρ hbranch j),
        ∀ y, (cover Y A F L u hvalid r ρ hbranch j).map (e.homeomorph y) =
          (cover Y A F L u hvalid r ρ hbranch i).map y := by
  let S := NativeCoverFamilyFiniteness.coverSetoid (Source Y A F L u hvalid r ρ hbranch)
    (differential Y A F L u hvalid r ρ hbranch) (cover Y A F L u hvalid r ρ hbranch)
  let : Finite (Quotient S) := finite_classes Y A F L u hvalid r ρ hbranch hdegree
  exact FiniteClassRepresentatives.exists_representatives S

end VeechDichotomy.VaryingNativeCoverFiniteness
