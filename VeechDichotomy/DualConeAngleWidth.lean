module

public import VeechDichotomy.PositiveConeAngleWidth
public import Mathlib.Analysis.Complex.Angle

/-! The actual angular width of the dual of a strict planar corner
is pi minus that corner's actual Euclidean angle. Explicit quarter-turn
boundary rays identify the entire dual cone with a positive two-ray cone.
The one-half-plane case has actual width pi. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DualConeAngleWidth

open Set ComplexOrientedTriangles HyperbolicRegionAngles

def dual (u v : ℂ) : Set ℂ := {w | inner ℝ u w ≤ 0 ∧ inner ℝ v w ≤ 0}
def halfPlane (u : ℂ) : Set ℂ := {w | inner ℝ u w ≤ 0}

theorem rotated_cross (u v : ℂ) : cross (Complex.I * u) (-Complex.I * v) = cross v u := by simp [cross]; ring

theorem left_cross (u w : ℂ) : cross (Complex.I * u) w = -inner ℝ u w := by
  rw [DirichletSiteNormals.complex_inner]
  simp [cross]
  ring

theorem right_cross (v w : ℂ) : cross w (-Complex.I * v) = -inner ℝ v w := by
  rw [DirichletSiteNormals.complex_inner]
  simp [cross]
  ring

theorem self_rotation (u : ℂ) : inner ℝ u (Complex.I * u) = 0 := by
  rw [DirichletSiteNormals.complex_inner]
  simp
  ring

theorem dual_eq_cone {u v : ℂ} (hD : 0 < cross v u) :
    dual u v = PositiveConeAngleWidth.cone (Complex.I * u) (-Complex.I * v) := by
  have hrot : 0 < cross (Complex.I * u) (-Complex.I * v) := by rwa [rotated_cross]
  apply Subset.antisymm
  · rintro w ⟨hu, hv⟩
    exact ComplexPositiveCones.combination _ _ _ hrot
      (by rw [left_cross]; exact neg_nonneg.mpr hu) (by rw [right_cross]; exact neg_nonneg.mpr hv)
  · intro w hw
    obtain ⟨α, β, hα, hβ, he⟩ := hw
    have hcrossuv : cross u v ≤ 0 := by rw [PositiveConeAngleWidth.cross_swap]; exact neg_nonpos.mpr hD.le
    have hu₁ : inner ℝ u (Complex.I * u) = 0 := self_rotation u
    have hu₂ : inner ℝ u (-Complex.I * v) = cross u v := by
      rw [DirichletSiteNormals.complex_inner]
      simp [cross]
      ring
    have hv₁ : inner ℝ v (Complex.I * u) = cross u v := by
      rw [DirichletSiteNormals.complex_inner]
      simp [cross]
      ring
    have hv₂ : inner ℝ v (-Complex.I * v) = 0 := by rw [neg_mul, inner_neg_right, self_rotation, neg_zero]
    change inner ℝ u w ≤ 0 ∧ inner ℝ v w ≤ 0
    rw [he, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, hu₁, hu₂, hv₁, hv₂]
    constructor
    · simpa only [mul_zero, zero_add] using mul_nonpos_of_nonneg_of_nonpos hβ hcrossuv
    · simpa only [mul_zero, add_zero] using mul_nonpos_of_nonneg_of_nonpos hα hcrossuv

theorem width_dual {u v : ℂ} (hD : 0 < cross v u) :
    vectorWidth (dual u v) = Real.pi - InnerProductGeometry.angle u v := by
  rw [dual_eq_cone hD, PositiveConeAngleWidth.width_eq (by rwa [rotated_cross]), neg_mul,
    InnerProductGeometry.angle_neg_right, Complex.angle_mul_left Complex.I_ne_zero]

theorem width_halfPlane (u : ℂ) (hu : u ≠ 0) : vectorWidth (halfPlane u) = Real.pi := by
  have hne : Complex.I * u ≠ 0 := mul_ne_zero Complex.I_ne_zero hu
  have hleft : Complex.I * u ∈ halfPlane u := (self_rotation u).le
  have hright : -(Complex.I * u) ∈ halfPlane u := by
    change inner ℝ u (-(Complex.I * u)) ≤ 0
    rw [inner_neg_right, self_rotation, neg_zero]
  apply le_antisymm (vectorWidth_le_pi _)
  apply le_csSup (vectorValues_bddAbove _)
  exact Or.inr ⟨Complex.I * u, -(Complex.I * u), hleft, hright, hne, neg_ne_zero.mpr hne,
    (InnerProductGeometry.angle_self_neg_of_nonzero hne).symm⟩

end VeechDichotomy.DualConeAngleWidth
