module

public import VeechDichotomy.HyperbolicTriangleAngleAddition

/-! Actual oriented area determinants and affine supporting half-planes
in the complex plane. Explicit determinant identities will identify
literal triangle regions and their common edges during triangulation. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ComplexOrientedTriangles

open Set

def cross (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re
def orient (a b c : ℂ) : ℝ := cross (b - a) (c - a)

@[simp] theorem orient_same_left (a b : ℂ) : orient a a b = 0 := by simp [orient, cross]
@[simp] theorem orient_same_right (a b : ℂ) : orient a b a = 0 := by simp [orient, cross]
@[simp] theorem orient_same_last (a b : ℂ) : orient a b b = 0 := by
  simp [orient, cross]
  ring

theorem orient_rotate (a b c : ℂ) : orient a b c = orient b c a := by
  simp only [orient, cross, Complex.sub_re, Complex.sub_im]
  ring

theorem orient_swap (a b c : ℂ) : orient a b c = -orient b a c := by
  simp only [orient, cross, Complex.sub_re, Complex.sub_im]
  ring

def side (a b : ℂ) : ℂ →L[ℝ] ℝ := (-(b.im - a.im)) • Complex.reCLM + (b.re - a.re) • Complex.imCLM

theorem orient_eq_side (a b z : ℂ) : orient a b z = side a b z - side a b a := by
  simp only [orient, cross, side, Complex.sub_re, Complex.sub_im, add_apply, smul_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  ring

theorem convex_halfPlane (a b : ℂ) : Convex ℝ {z : ℂ | 0 ≤ orient a b z} := by
  have heq : {z : ℂ | 0 ≤ orient a b z} = (side a b) ⁻¹' Ici (side a b a) := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_Ici, orient_eq_side, sub_nonneg]
  rw [heq]
  exact (convex_Ici _).linear_preimage (side a b).toLinearMap

theorem orientation_sum (a b c z : ℂ) :
    orient b c z + orient c a z + orient a b z = orient a b c := by
  simp only [orient, cross, Complex.sub_re, Complex.sub_im]
  ring

theorem weighted_identity (a b c z : ℂ) :
    (orient b c z) • a + (orient c a z) • b + (orient a b z) • c = (orient a b c) • z := by
  apply Complex.ext <;> simp [Complex.real_smul, orient, cross] <;> ring

theorem orient_combination (a b u v : ℂ) (s t : ℝ) (hst : s + t = 1) :
    orient a b (s • u + t • v) = s * orient a b u + t * orient a b v := by
  have hs : s = 1 - t := by linarith only [hst]
  rw [hs]
  simp [orient, cross, Complex.real_smul]
  ring

end VeechDichotomy.ComplexOrientedTriangles
