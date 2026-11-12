module

public import VeechDichotomy.HyperbolicFiniteTriangleAreaAngle
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-! Actual corner-angle addition inside a hyperbolic triangle. An
explicit real linear map sends Klein endpoint differences to positive
multiples of the fixed endpoint directions. Actual triangle membership
then puts the intermediate direction in the genuine nonnegative span,
and the proved Euclidean angle equality gives exact angle addition. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicTriangleAngleAddition

open Set HyperbolicKleinMap HyperbolicDirectionVectors HyperbolicIntrinsicAngles HyperbolicTriangles
open scoped UpperHalfPlane NNReal

set_option backward.isDefEq.respectTransparency false

def linear (a : ℍ) : ℂ →ₗ[ℝ] ℂ where
  toFun u := ⟨u.re + a.re * u.im,
    (-a.re * u.re + (denominator a / 2 - a.re ^ 2) * u.im) / a.im⟩
  map_add' u v := by apply Complex.ext <;> simp <;> ring
  map_smul' s u := by apply Complex.ext <;> simp [Complex.real_smul] <;> ring

def factor (b : ℍ) : ℝ := denominator b / 2

theorem factor_pos (b : ℍ) : 0 < factor b := div_pos (denominator_pos b) (by norm_num)

theorem direction_klein (a b : ℍ) : direction a b = factor b • linear a (point b - point a) := by
  rw [Complex.real_smul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change b.re - a.re = (denominator b / 2) *
      ((point b - point a).re + a.re * (point b - point a).im)
    simp only [Complex.sub_re, Complex.sub_im, point]
    field_simp [(denominator_pos a).ne', (denominator_pos b).ne']
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    change verticalCoefficient a b = (denominator b / 2) *
      ((-a.re * (point b - point a).re +
        (denominator a / 2 - a.re ^ 2) * (point b - point a).im) / a.im)
    simp only [Complex.sub_re, Complex.sub_im, point, verticalCoefficient]
    field_simp [(denominator_pos a).ne', (denominator_pos b).ne', a.im_ne_zero]
    rw [denominator_formula, denominator_formula]
    ring

theorem klein_difference_combination {a b c p : ℍ} (hp : p ∈ triangle a b c) :
    ∃ μ ν : ℝ, 0 ≤ μ ∧ 0 ≤ ν ∧
      point p - point a = μ • (point b - point a) + ν • (point c - point a) := by
  obtain ⟨q, hq, hpq⟩ := (mem_triangle_iff a b c p).mp hp
  have hq' := (HyperbolicKleinGeodesics.mem_metricSegment_iff b c q).mp hq
  have hp' := (HyperbolicKleinGeodesics.mem_metricSegment_iff a q p).mp hpq
  obtain ⟨α, β, hα, hβ, hαβ, hqeq⟩ := hq'
  obtain ⟨γ, δ, _, hδ, hγδ, hpeq⟩ := hp'
  refine ⟨δ * α, δ * β, mul_nonneg hδ hα, mul_nonneg hδ hβ, ?_⟩
  have hαeq : α = 1 - β := by linarith only [hαβ]
  have hγeq : γ = 1 - δ := by linarith only [hγδ]
  rw [← hpeq, ← hqeq, hαeq, hγeq]
  module

theorem direction_mem_span_of_combination {a b c p : ℍ} {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (he : point p - point a = μ • (point b - point a) + ν • (point c - point a)) :
    direction a p ∈ Submodule.span ℝ≥0 {direction a b, direction a c} := by
  have hb := factor_pos b
  have hc := factor_pos c
  have hpp := factor_pos p
  rw [Submodule.mem_span_pair]
  refine ⟨⟨factor p * μ / factor b, div_nonneg (mul_nonneg hpp.le hμ) hb.le⟩,
    ⟨factor p * ν / factor c, div_nonneg (mul_nonneg hpp.le hν) hc.le⟩, ?_⟩
  change (factor p * μ / factor b) • direction a b + (factor p * ν / factor c) • direction a c = direction a p
  rw [direction_klein a b, direction_klein a c, direction_klein a p, he, map_add, map_smul, map_smul]
  simp only [smul_smul, smul_add, div_mul_cancel₀ _ hb.ne', div_mul_cancel₀ _ hc.ne']

theorem direction_mem_span_of_klein {a b c p : ℍ}
    (hp : point p - point a ∈ Submodule.span ℝ≥0 {point b - point a, point c - point a}) :
    direction a p ∈ Submodule.span ℝ≥0 {direction a b, direction a c} := by
  rw [Submodule.mem_span_pair] at hp
  obtain ⟨μ, ν, he⟩ := hp
  apply direction_mem_span_of_combination μ.property ν.property
  simpa only [NNReal.smul_def] using! he.symm

theorem direction_mem_span {a b c p : ℍ} (hp : p ∈ triangle a b c) :
    direction a p ∈ Submodule.span ℝ≥0 {direction a b, direction a c} := by
  obtain ⟨μ, ν, hμ, hν, he⟩ := klein_difference_combination hp
  exact direction_mem_span_of_combination hμ hν he

theorem angle_addition_of_klein {a b c p : ℍ}
    (hp : point p - point a ∈ Submodule.span ℝ≥0 {point b - point a, point c - point a}) (hpa : p ≠ a) :
    angleAt a b c = angleAt a b p + angleAt a p c := by
  have hdir : direction a p ≠ 0 := fun he => hpa ((direction_eq_zero_iff a p).mp he).symm
  exact InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hdir (direction_mem_span_of_klein hp)

theorem angle_addition {a b c p : ℍ} (hp : p ∈ triangle a b c) (hpa : p ≠ a) :
    angleAt a b c = angleAt a b p + angleAt a p c := by
  have hdir : direction a p ≠ 0 := fun he => hpa ((direction_eq_zero_iff a p).mp he).symm
  exact InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hdir (direction_mem_span hp)

end VeechDichotomy.HyperbolicTriangleAngleAddition
