module

public import VeechDichotomy.KoopmanMeanErgodic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The actual Koopman mean preserves the integral. The constant-one
L2 vector is a proved fixed vector, so orthogonal projection preserves
its inner product with every observable. Indicator means therefore
integrate to the actual measure of the set. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.KoopmanMeanIntegral

open MeasureTheory Filter Topology KoopmanMeanErgodic

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → Ω) (hf : MeasurePreserving f μ μ)

theorem inner_limit_fixed (g h : Space μ) (hh : operator μ f hf h = h) :
    inner ℝ (limit μ f hf g) h = inner ℝ g h := by
  let K := (operator μ f hf).eqLocus (1 : Space μ →L[ℝ] Space μ)
  have hmem : h ∈ K := hh
  exact K.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨h, hmem⟩ g

variable [IsFiniteMeasure μ]

def constant (c : ℝ) : Space μ := (memLp_const c).toLp (fun _ : Ω => c)

theorem constant_ae (c : ℝ) : ⇑(constant μ c) =ᵐ[μ] fun _ => c :=
  MemLp.coeFn_toLp (memLp_const c)

theorem constant_fixed (c : ℝ) : operator μ f hf (constant μ c) = constant μ c := by
  apply Lp.ext
  change ⇑(Lp.compMeasurePreserving f hf (constant μ c)) =ᵐ[μ] ⇑(constant μ c)
  exact (Lp.coeFn_compMeasurePreserving (constant μ c) hf).trans
    ((hf.quasiMeasurePreserving.ae_eq_comp (constant_ae μ c)).trans (constant_ae μ c).symm)

theorem inner_constant_one (g : Space μ) : inner ℝ g (constant μ 1) = ∫ x, g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constant_ae μ 1] with x hx
  rw [hx, Real.inner_apply, mul_one]

theorem integral_limit (g : Space μ) : ∫ x, limit μ f hf g x ∂μ = ∫ x, g x ∂μ := by
  rw [← inner_constant_one μ (limit μ f hf g), inner_limit_fixed μ f hf g (constant μ 1) (constant_fixed μ f hf 1),
    inner_constant_one]

theorem indicator_integral_limit {B : Set Ω} (hB : MeasurableSet B) :
    ∫ x, limit μ f hf (indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)) x ∂μ = (μ B).toReal := by
  rw [integral_limit]
  calc
    (∫ x, indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) x ∂μ) =
        ∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂μ := integral_congr_ae indicatorConstLp_coeFn
    _ = (μ B).toReal := by simp [integral_indicator hB, Measure.real]

end VeechDichotomy.KoopmanMeanIntegral
