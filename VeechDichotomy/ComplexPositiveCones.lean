module

public import VeechDichotomy.HyperbolicFanAreas

/-! Actual nonnegative complex cones from determinant inequalities.
Explicit two-dimensional Cramer coefficients identify every vector
between two positively ordered rays as their nonnegative combination. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexPositiveCones

open ComplexOrientedTriangles
open scoped NNReal

theorem cramer_identity (u v w : ℂ) :
    (cross w v) • u + (cross u w) • v = (cross u v) • w := by
  apply Complex.ext <;> simp [cross, Complex.real_smul] <;> ring

theorem combination (u v w : ℂ) (hD : 0 < cross u v) (hleft : 0 ≤ cross u w) (hright : 0 ≤ cross w v) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ w = α • u + β • v := by
  refine ⟨cross w v / cross u v, cross u w / cross u v,
    div_nonneg hright hD.le, div_nonneg hleft hD.le, ?_⟩
  calc
    w = (1 / cross u v) • ((cross u v) • w) := by
      rw [smul_smul, one_div, inv_mul_cancel₀ hD.ne', one_smul]
    _ = (1 / cross u v) • ((cross w v) • u + (cross u w) • v) := by rw [cramer_identity]
    _ = _ := by
      simp only [smul_add, smul_smul, div_eq_mul_inv]
      module

theorem mem_span (u v w : ℂ) (hD : 0 < cross u v) (hleft : 0 ≤ cross u w) (hright : 0 ≤ cross w v) :
    w ∈ Submodule.span ℝ≥0 {u, v} := by
  obtain ⟨α, β, hα, hβ, he⟩ := combination u v w hD hleft hright
  rw [Submodule.mem_span_pair]
  refine ⟨⟨α, hα⟩, ⟨β, hβ⟩, ?_⟩
  simpa only [NNReal.smul_def] using! he.symm

end VeechDichotomy.ComplexPositiveCones
