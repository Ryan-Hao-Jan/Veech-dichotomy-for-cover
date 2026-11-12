module

public import VeechDichotomy.SL2Borel
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-! The genuine hyperbolic area dx dy / y^2 is positive on every
nonempty open set and invariant under the actual SL2 action. Strictly
positive continuous density over the actual complex area pullback proves
positivity; GL2 invariance restricts to SL2. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicAreaSupport

open LinearGroup MeasureTheory
open scoped UpperHalfPlane NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

instance area_openPos : (volume : Measure ℍ).IsOpenPosMeasure := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let : μ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap volume UpperHalfPlane.isOpenEmbedding_coe
  let d : ℍ → ℝ≥0 := fun z => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)
  have hd : Continuous d := by
    apply continuous_induced_rng.mpr
    change Continuous (fun z : ℍ => (1 / z.im) ^ 2)
    exact (continuous_const.div UpperHalfPlane.continuous_im (fun z => z.im_ne_zero)).pow 2
  have hd0 : ∀ z : ℍ, (d z : ℝ≥0∞) ≠ 0 := by
    intro z
    dsimp only [d]
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (div_ne_zero one_ne_zero (NNReal.ne_iff.mp z.im_ne_zero)))
  have hac : μ ≪ μ.withDensity (fun z => (d z : ℝ≥0∞)) :=
    withDensity_absolutelyContinuous' (ENNReal.continuous_coe.comp hd).measurable.aemeasurable
      (Filter.Eventually.of_forall hd0)
  change Measure.IsOpenPosMeasure (μ.withDensity (fun z => (d z : ℝ≥0∞)))
  exact hac.isOpenPosMeasure

instance area_sl2Invariant : SMulInvariantMeasure SL2 ℍ volume where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure ℍ))
      (Matrix.SpecialLinearGroup.mapGL ℝ g) hS

end VeechDichotomy.HyperbolicAreaSupport
