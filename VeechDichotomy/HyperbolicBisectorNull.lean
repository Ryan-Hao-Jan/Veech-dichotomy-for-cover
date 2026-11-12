module

public import VeechDichotomy.ComplexQuadraticNull
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-! Bisectors of two distinct genuine upper-half-plane points have zero
actual hyperbolic area. The explicit cosh-distance formula gives a real
circle/line polynomial with nonzero quadratic or linear coefficient.
Complex area nullness and the actual density definition transfer the result. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicBisectorNull

open Set MeasureTheory
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem volume_preimage_null {S : Set ℂ} (hS : (volume : Measure ℂ) S = 0) :
    (volume : Measure ℍ) (UpperHalfPlane.coe ⁻¹' S) = 0 := by
  rw [UpperHalfPlane.volume_def]
  apply withDensity_absolutelyContinuous
  rw [UpperHalfPlane.measurableEmbedding_coe.comap_apply]
  exact measure_mono_null (Set.image_preimage_subset UpperHalfPlane.coe S) hS

def leading (p q : ℍ) : ℝ := q.im - p.im
def linear (p q : ℍ) : ℝ := -2 * (q.im * p.re - p.im * q.re)
def constant (p q : ℍ) : ℝ := q.im * (p.re ^ 2 + p.im ^ 2) - p.im * (q.re ^ 2 + q.im ^ 2)

theorem coefficient_nontrivial {p q : ℍ} (hpq : p ≠ q) : leading p q ≠ 0 ∨ linear p q ≠ 0 := by
  by_cases ha : leading p q = 0
  · right
    intro hb
    have him : q.im = p.im := sub_eq_zero.mp ha
    have hprod : p.im * (p.re - q.re) = 0 := by
      dsimp only [linear] at hb
      rw [him] at hb
      nlinarith only [hb]
    have hre : p.re = q.re := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left p.im_ne_zero)
    apply hpq
    apply UpperHalfPlane.ext
    exact Complex.ext hre him.symm
  · exact Or.inl ha

theorem polynomial_eq_zero (p q z : ℍ) (hdist : dist z p = dist z q) :
    leading p q * Complex.normSq (z : ℂ) + linear p q * z.re + constant p q = 0 := by
  have hc := congrArg Real.cosh hdist
  rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist] at hc
  have hf : dist (z : ℂ) (p : ℂ) ^ 2 / (2 * z.im * p.im) =
      dist (z : ℂ) (q : ℂ) ^ 2 / (2 * z.im * q.im) := add_left_cancel hc
  have hp : 2 * z.im * p.im ≠ 0 := by positivity
  have hq : 2 * z.im * q.im ≠ 0 := by positivity
  have hcross := (div_eq_div_iff hp hq).mp hf
  have hzero : (2 * z.im) * (q.im * dist (z : ℂ) (p : ℂ) ^ 2 -
      p.im * dist (z : ℂ) (q : ℂ) ^ 2) = 0 := by nlinarith only [hcross]
  have hcoef : q.im * dist (z : ℂ) (p : ℂ) ^ 2 - p.im * dist (z : ℂ) (q : ℂ) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (by positivity)
  simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hcoef
  dsimp only [leading, linear, constant]
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith only [hcoef]

def bisector (p q : ℍ) : Set ℍ := {z | dist z p = dist z q}

theorem isClosed_bisector (p q : ℍ) : IsClosed (bisector p q) :=
  isClosed_eq (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

theorem volume_bisector {p q : ℍ} (hpq : p ≠ q) : volume (bisector p q) = 0 := by
  let S : Set ℂ := {z | leading p q * Complex.normSq z + linear p q * z.re + constant p q = 0}
  have hS : (volume : Measure ℂ) S = 0 :=
    ComplexQuadraticNull.quadratic_null _ _ _ (coefficient_nontrivial hpq)
  apply measure_mono_null (t := UpperHalfPlane.coe ⁻¹' S) _ (volume_preimage_null hS)
  intro z hz
  exact polynomial_eq_zero p q z hz

end VeechDichotomy.HyperbolicBisectorNull
