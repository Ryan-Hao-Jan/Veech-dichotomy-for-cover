module

public import VeechDichotomy.UniformSL2ConfigurationLimits
public import VeechDichotomy.NativePuncturedFundamentalGroup

/-! Compact actual matrix and distinct-configuration sets give one
uniform marked parameter domain and convergent concrete parameters for
a subsequence. The transports recover the original branch tuples exactly. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CompactSL2ConfigurationParameters

open MNEC.NativeAbelianDifferential BeltramiPlane LinearGroup Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiConfigurationCoordinates
open UniformSL2ConfigurationParameters
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}

theorem subsequence (q : Differential X) (L : ℕ → SL2) (u : ℕ → Fin m → X)
    {K : Set SL2} (hK : IsCompact K) (hL : ∀ n, L n ∈ K)
    {C : Set (Fin m → X)} (hC : IsCompact C) (hu : ∀ n, u n ∈ C) (hconf : C ⊆ configuration m X) :
    ∃ L₀ ∈ K, ∃ b ∈ C, ∃ A : Data q b (SL2BeltramiParameters.parameter L₀), ∃ F : Family A,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (L ∘ σ) atTop (𝓝 L₀) ∧ Tendsto (u ∘ σ) atTop (𝓝 b) ∧
        ∃ hvalid : ∀ n, Valid A (SL2BeltramiParameters.parameter (L (σ n))) (u (σ n)),
          Tendsto (fun n => familyParameters A (L (σ n)) (u (σ n)) (hvalid n)) atTop
            (𝓝 ((NativeSL2AnalyticFamily.parameters L₀).1, ComplexBeltramiMarkParameters.reference A)) ∧
          ∀ n, tuple A F (markParameters A (L (σ n)) (u (σ n)) (hvalid n)) = u (σ n) := by
  let : SecondCountableTopology X := ChartedSpace.secondCountable_of_sigmaCompact ℂ X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let : FirstCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → ℝ))
  let : FirstCountableTopology SL2 := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.firstCountableTopology
  obtain ⟨v, hv, τ, hτ, hconv⟩ := (hK.prod hC).tendsto_subseq
    (x := fun n => (L n, u n)) (fun n => ⟨hL n, hu n⟩)
  have hLτ : Tendsto (L ∘ τ) atTop (𝓝 v.1) := continuous_fst.continuousAt.tendsto.comp hconv
  have huτ : Tendsto (u ∘ τ) atTop (𝓝 v.2) := continuous_snd.continuousAt.tendsto.comp hconv
  let A := chosenData q v.2 (SL2BeltramiParameters.parameter v.1) (hconf hv.2)
  let F := chosenFamily A
  obtain ⟨υ, hυ, hvalid, hpconv⟩ := UniformSL2ConfigurationLimits.eventually_parameters A (L ∘ τ) (u ∘ τ) v.1 rfl hLτ huτ
  refine ⟨v.1, hv.1, v.2, hv.2, A, F, τ ∘ υ, hτ.comp hυ,
    hLτ.comp hυ.tendsto_atTop, huτ.comp hυ.tendsto_atTop, hvalid, hpconv, ?_⟩
  intro n
  exact parameters_moves A F (SL2BeltramiParameters.parameter (L (τ (υ n)))) (u (τ (υ n))) (hvalid n)

end VeechDichotomy.CompactSL2ConfigurationParameters
