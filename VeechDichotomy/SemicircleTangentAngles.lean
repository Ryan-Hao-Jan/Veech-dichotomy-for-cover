module

public import VeechDichotomy.NormalizedIdealTriangleAngles

/-! The angle between actual unit semicircle tangents is the absolute
difference of their actual arcsine parameters. Actual unit norms and
the real inner product identify its cosine; the proved inverse-cosine
branch bounds recover the angle, including both parameter orders. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SemicircleTangentAngles

open NormalizedIdealTriangleCoordinates NormalizedTriangleTangents

theorem inner_left (x y : ℝ) :
    inner ℝ (leftTangent x) (leftTangent y) = height x * height y + x * y := by
  simp [real_inner_eq_re_inner ℂ, RCLike.inner_apply, leftTangent]
  ring

theorem left_angle {x y : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) (hy₀ : -1 < y) (hy₁ : y < 1) :
    InnerProductGeometry.angle (leftTangent x) (leftTangent y) =
      |Real.arcsin x - Real.arcsin y| := by
  rw [InnerProductGeometry.angle, inner_left, leftTangent_norm hx₀ hx₁,
    leftTangent_norm hy₀ hy₁, one_mul, div_one]
  have hbound : |Real.arcsin x - Real.arcsin y| ≤ Real.pi := by
    apply abs_le.mpr
    have hx := Real.arcsin_mem_Icc x
    have hy := Real.arcsin_mem_Icc y
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  apply Real.arccos_eq_of_eq_cos (abs_nonneg _) hbound
  rw [Real.cos_abs, Real.cos_sub, Real.cos_arcsin, Real.cos_arcsin,
    Real.sin_arcsin hx₀.le hx₁.le, Real.sin_arcsin hy₀.le hy₁.le]
  rfl

theorem right_angle {x y : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) (hy₀ : -1 < y) (hy₁ : y < 1) :
    InnerProductGeometry.angle (rightTangent x) (rightTangent y) =
      |Real.arcsin x - Real.arcsin y| := by
  rw [rightTangent, rightTangent, InnerProductGeometry.angle_neg_neg]
  exact left_angle hx₀ hx₁ hy₀ hy₁

theorem right_angle_of_le {x y : ℝ} (hx₀ : -1 < x) (hx₁ : x < 1) (hy₀ : -1 < y) (hy₁ : y < 1)
    (hxy : x ≤ y) : InnerProductGeometry.angle (rightTangent x) (rightTangent y) =
      Real.arcsin y - Real.arcsin x := by
  rw [right_angle hx₀ hx₁ hy₀ hy₁, abs_of_nonpos (sub_nonpos.mpr (Real.monotone_arcsin hxy))]
  ring

end VeechDichotomy.SemicircleTangentAngles
