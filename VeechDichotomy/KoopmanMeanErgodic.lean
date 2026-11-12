module

public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A measure-preserving map gives an ACTUAL L2 Koopman isometry.
The proved Hilbert-space mean ergodic theorem supplies its averaged
limit and actual almost-everywhere subsequences, with no ergodicity
or finite-spectrum assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KoopmanMeanErgodic

open MeasureTheory Filter Topology

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → Ω) (hf : MeasurePreserving f μ μ)

abbrev Space := Lp ℝ 2 μ

def operator : Space μ →L[ℝ] Space μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap

set_option maxHeartbeats 800000 in
theorem operator_norm_le : ‖operator μ f hf‖ ≤ 1 := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := 2) f hf).toContinuousLinearMap‖ ≤ 1
  exact (Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := 2) f hf).norm_toContinuousLinearMap_le

def average (g : Space μ) (n : ℕ) : Space μ :=
  birkhoffAverage ℝ (operator μ f hf) id n g

def limit (g : Space μ) : Space μ :=
  ((operator μ f hf).eqLocus (1 : Space μ →L[ℝ] Space μ)).orthogonalProjectionOnto g

theorem limit_fixed (g : Space μ) : operator μ f hf (limit μ f hf g) = limit μ f hf g :=
  (((operator μ f hf).eqLocus (1 : Space μ →L[ℝ] Space μ)).orthogonalProjectionOnto g).property

theorem tendsto_average (g : Space μ) :
    Tendsto (average μ f hf g) atTop (𝓝 (limit μ f hf g)) :=
  (operator μ f hf).tendsto_birkhoffAverage_orthogonalProjection (operator_norm_le μ f hf) g

theorem ae_subsequence (g : Space μ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => average μ f hf g (n (σ k)) x) atTop (𝓝 (limit μ f hf g x)) :=
  (tendstoInMeasure_of_tendsto_Lp ((tendsto_average μ f hf g).comp hn)).exists_seq_tendsto_ae

end VeechDichotomy.KoopmanMeanErgodic
