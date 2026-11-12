module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Actual complex area vanishes on a nontrivial circle-or-vertical-line
quadratic A*normSq(z)+B*re(z)+C=0. For A nonzero, completing the square
puts the set on an actual Euclidean sphere. Otherwise its real part is
fixed, and the genuine complex/product area equivalence proves nullness. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexQuadraticNull

open Set MeasureTheory

theorem vertical_null (r : ℝ) : (volume : Measure ℂ) {z | z.re = r} = 0 := by
  have heq : {z : ℂ | z.re = r} = Complex.measurableEquivRealProd ⁻¹' ({r} ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton r).prod MeasurableSet.univ).nullMeasurableSet]
  change (volume : Measure ℝ).prod (volume : Measure ℝ) ({r} ×ˢ (univ : Set ℝ)) = 0
  simp

theorem quadratic_null (A B C : ℝ) (hab : A ≠ 0 ∨ B ≠ 0) :
    (volume : Measure ℂ) {z | A * Complex.normSq z + B * z.re + C = 0} = 0 := by
  let E : Set ℂ := {z | A * Complex.normSq z + B * z.re + C = 0}
  change (volume : Measure ℂ) E = 0
  by_cases ha : A = 0
  · have hb : B ≠ 0 := hab.resolve_left (not_ne_iff.mpr ha)
    apply measure_mono_null (t := {z : ℂ | z.re = -C / B}) _ (vertical_null _)
    intro z hz
    change A * Complex.normSq z + B * z.re + C = 0 at hz
    have he : B * z.re + C = 0 := by simpa only [ha, zero_mul, zero_add] using hz
    apply (eq_div_iff hb).mpr
    linarith
  · rcases E.eq_empty_or_nonempty with he | ⟨z₀, hz₀⟩
    · rw [he, measure_empty]
    · let c : ℂ := (-B / (2 * A) : ℝ)
      have hnorm (z : ℂ) (hz : z ∈ E) : ‖z - c‖ = ‖z₀ - c‖ := by
        have hid : A * (Complex.normSq (z - c) - Complex.normSq (z₀ - c)) =
            (A * Complex.normSq z + B * z.re + C) - (A * Complex.normSq z₀ + B * z₀.re + C) := by
          simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, c, Complex.ofReal_re, Complex.ofReal_im]
          field_simp [ha]
          ring
        have hprod : A * (Complex.normSq (z - c) - Complex.normSq (z₀ - c)) = 0 := by
          rw [hid, hz, hz₀, sub_self]
        have hsq : ‖z - c‖ ^ 2 = ‖z₀ - c‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.sq_norm]
          exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha)
        exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
      apply measure_mono_null (t := Metric.sphere c ‖z₀ - c‖) _ (Measure.addHaar_sphere volume c _)
      intro z hz
      rw [Metric.mem_sphere, dist_eq_norm]
      exact hnorm z hz

end VeechDichotomy.ComplexQuadraticNull
