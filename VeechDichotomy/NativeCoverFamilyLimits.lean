module

public import VeechDichotomy.NativeVaryingBaseCoverCompactness

/-! A name for the explicit family-limit conclusion already proved by
native varying-base cover compactness. It retains the actual constructed
family, converging parameters, true native differential equivalences and
covering squares. It introduces no new topology or existence premise. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCoverFamilyLimits

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeDeformationRegular WholeDeformedAtlas LinearGroup BeltramiPlane
open Set Filter Topology UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open UniformSL2ConfigurationParameters VaryingNativeCoverExhaustion
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} (Y : ℕ → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {q : Differential X} {m : ℕ} (L : ℕ → SL2) (u : ℕ → Fin m → X) (r : ∀ i, Differential (Y i))

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (ρ : ∀ i, Cover (transformed q (L i)) (r i))
  (hbranch : ∀ i, branchValues (ρ i) = range (fun k => (toOriginal q (L i)).symm (u i k)))

def FamilyLimit (K : Set SL2) (C : Set (Fin m → X)) : Prop :=
  ∃ L₀ ∈ K, ∃ b ∈ C, ∃ A : Data q b (SL2BeltramiParameters.parameter L₀), ∃ F : Family A,
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ hvalid : ∀ n, Valid A (SL2BeltramiParameters.parameter (L (σ n))) (u (σ n)),
        ∃ j : ℕ, ∃ τ : ℕ → ℕ, StrictMono τ ∧
          Tendsto (fun n => familyParameters A (L (σ (τ n))) (u (σ (τ n))) (hvalid (τ n))) atTop
            (𝓝 ((NativeSL2AnalyticFamily.parameters L₀).1, ComplexBeltramiMarkParameters.reference A)) ∧
          ∀ n, ∃ e : MNEC.NativeDifferentialEquiv.Equiv (r (σ (τ n)))
            (familyDifferential (fun k => Y (σ k)) A F (L ∘ σ) (u ∘ σ) hvalid (fun k => r (σ k))
              (fun k => ρ (σ k)) (fun k => hbranch (σ k)) j
              (familyParameters A (L (σ (τ n))) (u (σ (τ n))) (hvalid (τ n)))),
            ∀ y, (familyCover (fun k => Y (σ k)) A F (L ∘ σ) (u ∘ σ) hvalid (fun k => r (σ k))
              (fun k => ρ (σ k)) (fun k => hbranch (σ k)) j
              (familyParameters A (L (σ (τ n))) (u (σ (τ n))) (hvalid (τ n)))).map (e.homeomorph y) =
                (baseEquivalence A (L (σ (τ n))) (u (σ (τ n))) (hvalid (τ n))).homeomorph ((ρ (σ (τ n))).map y)

theorem family_limit {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (ρ i) = d)
    {K : Set SL2} (hK : IsCompact K) (hL : ∀ n, L n ∈ K)
    {C : Set (Fin m → X)} (hC : IsCompact C) (hu : ∀ n, u n ∈ C) (hconf : C ⊆ configuration m X) :
    FamilyLimit Y L u r ρ hbranch K C :=
  NativeVaryingBaseCoverCompactness.subsequence Y L u r ρ hbranch hdegree hK hL hC hu hconf

end VeechDichotomy.NativeCoverFamilyLimits
