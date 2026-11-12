module

public import VeechDichotomy.KoopmanMeanErgodic

/-! The Hilbert-space averages are ACTUAL pointwise orbit averages
almost everywhere. This identifies their representatives and supplies
fixed-source-point statistical limits along genuine subsequences. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KoopmanPointwiseAverages

open MeasureTheory Filter Topology Finset KoopmanMeanErgodic

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → Ω) (hf : MeasurePreserving f μ μ)

theorem operator_iterate (g : Space μ) (n : ℕ) :
    (operator μ f hf)^[n] g = Lp.compMeasurePreserving f^[n] (hf.iterate n) g := by
  change (Lp.compMeasurePreserving f hf)^[n] g = _
  rw [Lp.compMeasurePreserving_iterate]

theorem iterate_ae (g : Space μ) (n : ℕ) :
    ⇑((operator μ f hf)^[n] g) =ᵐ[μ] fun x => g (f^[n] x) := by
  rw [operator_iterate]
  exact Lp.coeFn_compMeasurePreserving g (hf.iterate n)

theorem average_ae (g : Space μ) (n : ℕ) :
    ⇑(average μ f hf g n) =ᵐ[μ] birkhoffAverage ℝ f (g : Ω → ℝ) n := by
  have hscalar := Lp.coeFn_smul ((n : ℝ)⁻¹) (∑ k ∈ range n, (operator μ f hf)^[k] g)
  have hsum := Lp.coeFn_fun_finsetSum (range n) (fun k => (operator μ f hf)^[k] g)
  have hit : ∀ᵐ x ∂μ, ∀ k : ℕ, ((operator μ f hf)^[k] g) x = g (f^[k] x) :=
    ae_all_iff.mpr (iterate_ae μ f hf g)
  filter_upwards [hscalar, hsum, hit] with x hxScalar hxSum hxIterate
  change (((n : ℝ)⁻¹) • ∑ k ∈ range n, (operator μ f hf)^[k] g) x = _
  rw [hxScalar, Pi.smul_apply, hxSum]
  change (n : ℝ)⁻¹ * (∑ k ∈ range n, ((operator μ f hf)^[k] g) x) = _
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  congr 1
  exact sum_congr rfl (fun k _ => hxIterate k)

theorem averages_ae_all (g : Space μ) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, average μ f hf g n x = birkhoffAverage ℝ f (g : Ω → ℝ) n x :=
  ae_all_iff.mpr (average_ae μ f hf g)

theorem limit_invariant_ae (g : Space μ) :
    (fun x => limit μ f hf g (f x)) =ᵐ[μ] (limit μ f hf g : Ω → ℝ) := by
  have h := Lp.coeFn_compMeasurePreserving (limit μ f hf g) hf
  change ⇑(operator μ f hf (limit μ f hf g)) =ᵐ[μ] _ at h
  rw [limit_fixed] at h
  exact h.symm

theorem ae_pointwise_subsequence (g : Space μ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ x ∂μ,
      Tendsto (fun k => birkhoffAverage ℝ f (g : Ω → ℝ) (n (σ k)) x) atTop (𝓝 (limit μ f hf g x)) := by
  obtain ⟨σ, hσ, hlim⟩ := ae_subsequence μ f hf g n hn
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hlim, averages_ae_all μ f hf g] with x hx hrep
  exact Tendsto.congr (fun k => hrep (n (σ k))) hx

end VeechDichotomy.KoopmanPointwiseAverages
