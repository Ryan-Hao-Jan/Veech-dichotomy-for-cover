module

public import VeechDichotomy.CountableKoopmanProfiles
public import VeechDichotomy.FlowAverageFloor
public import VeechDichotomy.FlowBlockIntegral

/-! Actual continuous-time statistical profiles for bounded measurable
observables of continuous measure-preserving flows. Countably many flows,
measures, observables and diverging REAL time scales share one strictly
increasing a.e. convergent subsequence. The mean retains the original
observable's integral; ergodicity and finite ergodic spectra are not inputs. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FlowContinuousProfiles

open MeasureTheory Filter Topology FlowUnitBlock FlowIntegerAverages

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

def mean (F : Flow ℝ Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (hF : ∀ s, MeasurePreserving (F s) μ μ)
    (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) : KoopmanMeanErgodic.Space μ :=
  KoopmanMeanErgodic.limit μ (F 1) (hF 1) (blockLp F g μ hg C hbound)

theorem mean_integral (F : Flow ℝ Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (hF : ∀ s, MeasurePreserving (F s) μ μ)
    (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    ∫ x, mean F μ hF g hg C hbound x ∂μ = ∫ x, g x ∂μ :=
  FlowBlockIntegral.mean_integral F μ hF g hg C hbound

theorem profiles (μ : ℕ → Measure Ω) [∀ j, IsFiniteMeasure (μ j)] (F : ℕ → Flow ℝ Ω)
    (hF : ∀ j s, MeasurePreserving (F j s) (μ j) (μ j))
    (g : ℕ → Ω → ℝ) (hg : ∀ j, Measurable (g j)) (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hbound : ∀ j x, ‖g j x‖ ≤ C j) (T : ℕ → ℕ → ℝ) (hT : ∀ j, Tendsto (T j) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, ∀ᵐ x ∂μ j,
      Tendsto (fun k => timeAverage (F j) (g j) (T j (σ k)) x) atTop
        (𝓝 (mean (F j) (μ j) (hF j) (g j) (hg j) (C j) (hbound j) x)) := by
  have hn : ∀ j, Tendsto (fun k => Nat.floor (T j k)) atTop atTop :=
    fun j => tendsto_nat_floor_atTop.comp (hT j)
  obtain ⟨σ, hσ, hlim⟩ := CountableKoopmanProfiles.simultaneous μ (fun j => F j 1) (fun j => hF j 1)
    (fun j => blockLp (F j) (g j) (μ j) (hg j) (C j) (hbound j)) (fun j k => Nat.floor (T j k)) hn
  refine ⟨σ, hσ, ?_⟩
  intro j
  filter_upwards [hlim j, block_pointwise_averages_ae (F j) (g j) (μ j) (hF j 1) (hg j) (C j) (hbound j)] with x hx hrep
  have hfloor : Tendsto (fun k => timeAverage (F j) (g j) (Nat.floor (T j (σ k)) : ℝ) x) atTop
      (𝓝 (mean (F j) (μ j) (hF j) (g j) (hg j) (C j) (hbound j) x)) :=
    Tendsto.congr (fun k => hrep (Nat.floor (T j (σ k)))) hx
  exact FlowAverageFloor.tendsto_of_floor (F j) (g j) (hg j) (C j) (hC j) (hbound j)
    ((hT j).comp hσ.tendsto_atTop) x hfloor

end VeechDichotomy.FlowContinuousProfiles
