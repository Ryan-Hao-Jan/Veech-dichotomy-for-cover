module

public import VeechDichotomy.KoopmanPointwiseAverages
public import VeechDichotomy.CountableConvergenceInMeasure

/-! Countably many actual orbit-average profiles converge almost
everywhere along ONE common subsequence. Each profile may use its own
measure, preserving transformation, L2 observable and diverging integer
time scale. All convergence inputs come from the proved Koopman theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CountableKoopmanProfiles

open MeasureTheory Filter Topology

theorem simultaneous {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (f : ℕ → Ω → Ω) (hf : ∀ j, MeasurePreserving (f j) (μ j) (μ j))
    (g : ∀ j, KoopmanMeanErgodic.Space (μ j)) (n : ℕ → ℕ → ℕ) (hn : ∀ j, Tendsto (n j) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, ∀ᵐ x ∂μ j,
      Tendsto (fun k => birkhoffAverage ℝ (f j) (g j : Ω → ℝ) (n j (σ k)) x) atTop
        (𝓝 (KoopmanMeanErgodic.limit (μ j) (f j) (hf j) (g j) x)) := by
  have hconv : ∀ j, TendstoInMeasure (μ j)
      (fun k => KoopmanMeanErgodic.average (μ j) (f j) (hf j) (g j) (n j k)) atTop
      (KoopmanMeanErgodic.limit (μ j) (f j) (hf j) (g j)) :=
    fun j => tendstoInMeasure_of_tendsto_Lp ((KoopmanMeanErgodic.tendsto_average (μ j) (f j) (hf j) (g j)).comp (hn j))
  obtain ⟨σ, hσ, hlim⟩ := CountableConvergenceInMeasure.simultaneous μ _ _ hconv
  refine ⟨σ, hσ, ?_⟩
  intro j
  filter_upwards [hlim j, KoopmanPointwiseAverages.averages_ae_all (μ j) (f j) (hf j) (g j)] with x hx hrep
  exact Tendsto.congr (fun k => hrep (n j (σ k))) hx

end VeechDichotomy.CountableKoopmanProfiles
