module

public import VeechDichotomy.ConvergentConfigurationParameters
public import VeechDichotomy.NativeAnalyticCoverSequentialCompactness
public import VeechDichotomy.NativeAnalyticCoverCoefficients

/-! Fixed-base native cover compactness in actual analytic families.
For a fixed degree and branch tuples in any compact subset of the distinct
configuration locus, a subsequence lies in ONE constructed proper analytic
family with complex parameter tending to zero and an actual native limit
fiber. Every comparison preserves the true differential and covering map.
This is a family-limit theorem, not a definition of a convenient moduli topology. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFixedBaseCoverCompactness

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open ComplexDisplacementParameters NativeAnalyticCoverExhaustion Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} (Y : ℕ → Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, CompactSpace (Y i)]
  [∀ i, ConnectedSpace (Y i)] [∀ i, ChartedSpace ℂ (Y i)] [∀ i, IsManifold 𝓘(ℂ) ω (Y i)]
variable {ωX : Differential X} (ωY : ∀ i, Differential (Y i)) (π : ∀ i, Cover ωX (ωY i))
variable {m : ℕ} (branches : ℕ → Fin m → X)

theorem subsequence {d : ℕ} (hdegree : ∀ i, NativeFullCoverDegree.degree (π i) = d)
    (hBranch : ∀ n, range (branches n) = branchValues (π n))
    {F : Set (Fin m → X)} (hF : IsCompact F) (hmem : ∀ n, branches n ∈ F)
    (hconf : F ⊆ configuration m X) :
    ∃ b ∈ F, ∃ A : Data b, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → Parameters m,
      Tendsto a atTop (𝓝 (zero m)) ∧
      ∃ hLocal : ∀ n, branchValues (π (σ n)) = range (A.tuple (a n)).val,
      ∃ j : ℕ, ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto (a ∘ τ) atTop (𝓝 (zero m)) ∧
        ∀ n, ∃ e : MNEC.NativeDifferentialEquiv.Equiv (ωY (σ (τ n)))
          (familyDifferential (fun k => Y (σ k)) (fun k => ωY (σ k)) (fun k => π (σ k)) b A a hLocal j (a (τ n))),
          ∀ y, (familyCover (fun k => Y (σ k)) (fun k => ωY (σ k)) (fun k => π (σ k)) b A a hLocal j (a (τ n))).map
            (e.homeomorph y) = (π (σ (τ n))).map y := by
  obtain ⟨b, hb, A, σ, hσ, a, ha, htuple⟩ :=
    ConvergentConfigurationParameters.compact_configuration_subsequence ωX branches hF hmem hconf
  have hLocal (n : ℕ) : branchValues (π (σ n)) = range (A.tuple (a n)).val := by
    rw [htuple n]
    exact (hBranch (σ n)).symm
  obtain ⟨j, τ, hτ, hconv, hequiv⟩ := NativeAnalyticCoverSequentialCompactness.subsequence_of_tendsto
    (fun k => Y (σ k)) (fun k => ωY (σ k)) (fun k => π (σ k)) b A a hLocal (fun k => hdegree (σ k)) ha
  exact ⟨b, hb, A, σ, hσ, a, ha, hLocal, j, τ, hτ, hconv, hequiv⟩

theorem zero_branch_values (b : Fin m → X) (A : Data b) (a : ℕ → Parameters m)
    (hLocal : ∀ i, branchValues (π i) = range (A.tuple (a i)).val) (j : ℕ) :
    branchValues (familyCover Y ωY π b A a hLocal j (zero m)) = range b := by
  rw [NativeAnalyticCoverSequentialCompactness.limit_branch_values,
    ConvergentConfigurationParameters.tuple_zero]

theorem zero_degree (b : Fin m → X) (A : Data b) (a : ℕ → Parameters m)
    (hLocal : ∀ i, branchValues (π i) = range (A.tuple (a i)).val) {d : ℕ}
    (hdegree : ∀ i, NativeFullCoverDegree.degree (π i) = d) (j : ℕ) :
    NativeFullCoverDegree.degree (familyCover Y ωY π b A a hLocal j (zero m)) = d :=
  (NativeAnalyticCoverSequentialCompactness.limit_degree Y ωY π b A a hLocal j (zero m)).trans (hdegree j)

end VeechDichotomy.NativeFixedBaseCoverCompactness
