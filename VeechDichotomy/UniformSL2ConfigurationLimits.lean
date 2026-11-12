module

public import VeechDichotomy.UniformSL2ConfigurationParameters

/-! Concrete matrix/branch parameters converge in the actual scalar
extended marked domain. A single tail provides every validity proof;
the parameters are computed from the GIVEN matrices and tuples. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformSL2ConfigurationLimits

open MNEC.NativeAbelianDifferential BeltramiPlane LinearGroup Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiConfigurationCoordinates UniformSL2ConfigurationParameters
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data q b μ₀)

theorem parameters_tendsto (L : ℕ → SL2) (u : ℕ → Fin m → X) (L₀ : SL2)
    (hcenter : SL2BeltramiParameters.parameter L₀ = μ₀)
    (hL : Tendsto L atTop (𝓝 L₀)) (hu : Tendsto u atTop (𝓝 b))
    (hvalid : ∀ n, Valid A (SL2BeltramiParameters.parameter (L n)) (u n)) :
    Tendsto (fun n => familyParameters A (L n) (u n) (hvalid n)) atTop
      (𝓝 ((NativeSL2AnalyticFamily.parameters L₀).1, ComplexBeltramiMarkParameters.reference A)) := by
  have hμ : Tendsto (fun n => SL2BeltramiParameters.parameter (L n)) atTop (𝓝 μ₀) := by
    have h := SL2BeltramiParameters.continuous_parameter.continuousAt.tendsto.comp hL
    rwa [hcenter] at h
  have hmark : Tendsto (fun n => markParameters A (L n) (u n) (hvalid n)) atTop
      (𝓝 (ComplexBeltramiMarkParameters.reference A)) :=
    tendsto_subtype_rng.mpr (ConvergentBeltramiConfigurationParameters.raw_tendsto A _ u hμ hu)
  have hscalar := (continuous_fst.comp NativeSL2AnalyticFamily.continuous_parameters).continuousAt.tendsto.comp hL
  exact hscalar.prodMk_nhds hmark

theorem eventually_parameters (L : ℕ → SL2) (u : ℕ → Fin m → X) (L₀ : SL2)
    (hcenter : SL2BeltramiParameters.parameter L₀ = μ₀)
    (hL : Tendsto L atTop (𝓝 L₀)) (hu : Tendsto u atTop (𝓝 b)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ hvalid : ∀ n, Valid A (SL2BeltramiParameters.parameter (L (σ n))) (u (σ n)),
        Tendsto (fun n => familyParameters A (L (σ n)) (u (σ n)) (hvalid n)) atTop
          (𝓝 ((NativeSL2AnalyticFamily.parameters L₀).1, ComplexBeltramiMarkParameters.reference A)) := by
  have hμ : Tendsto (fun n => SL2BeltramiParameters.parameter (L n)) atTop (𝓝 μ₀) := by
    have h := SL2BeltramiParameters.continuous_parameter.continuousAt.tendsto.comp hL
    rwa [hcenter] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ConvergentBeltramiConfigurationParameters.eventually_valid A _ u hμ hu)
  let σ : ℕ → ℕ := fun n => n + N
  have hσ : StrictMono σ := fun _ _ h => Nat.add_lt_add_right h N
  let hvalid : ∀ n, Valid A (SL2BeltramiParameters.parameter (L (σ n))) (u (σ n)) :=
    fun n => hN (σ n) (Nat.le_add_left N n)
  exact ⟨σ, hσ, hvalid, parameters_tendsto A (L ∘ σ) (u ∘ σ) L₀ hcenter
    (hL.comp hσ.tendsto_atTop) (hu.comp hσ.tendsto_atTop) hvalid⟩

end VeechDichotomy.UniformSL2ConfigurationLimits
