module

public import VeechDichotomy.HyperbolicDistanceComparison

/-! Every genuine distinct-point hyperbolic bisector is exactly a
vertical line or an upper semicircle centered on the real axis with
strictly positive radius. All parameters come from the actual distance
polynomial; the discriminant and square completion are explicitly proved. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicBisectorShapes

open HyperbolicBisectorNull HyperbolicDistanceComparison Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def vertical (c : ℝ) : Set ℍ := {z | z.re = c}
def semicircle (c r : ℝ) : Set ℍ := {z | ‖(z : ℂ) - (c : ℂ)‖ = r}

def center (p q : ℍ) : ℝ := -linear p q / (2 * leading p q)
def radiusSq (p q : ℍ) : ℝ := (linear p q ^ 2 - 4 * leading p q * constant p q) / (4 * leading p q ^ 2)
def radius (p q : ℍ) : ℝ := Real.sqrt (radiusSq p q)

theorem discriminant_formula (p q : ℍ) :
    linear p q ^ 2 - 4 * leading p q * constant p q =
      4 * p.im * q.im * ((p.re - q.re) ^ 2 + (p.im - q.im) ^ 2) := by
  dsimp only [linear, leading, constant]
  ring

theorem radiusSq_pos {p q : ℍ} (ha : leading p q ≠ 0) : 0 < radiusSq p q := by
  have hi : p.im - q.im ≠ 0 := by
    intro he
    apply ha
    dsimp only [leading]
    linarith
  have hsum : 0 < (p.re - q.re) ^ 2 + (p.im - q.im) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hi)
  dsimp only [radiusSq]
  apply div_pos
  · rw [discriminant_formula]
    exact mul_pos (mul_pos (mul_pos (by norm_num) p.im_pos) q.im_pos) hsum
  · exact mul_pos (by norm_num) (sq_pos_of_ne_zero ha)

theorem complete_square {p q : ℍ} (ha : leading p q ≠ 0) (z : ℂ) :
    form p q z = leading p q * (Complex.normSq (z - (center p q : ℂ)) - radiusSq p q) := by
  dsimp only [form, center, radiusSq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp [ha]
  ring

theorem bisector_vertical {p q : ℍ} (hpq : p ≠ q) (ha : leading p q = 0) :
    bisector p q = vertical (-constant p q / linear p q) := by
  have hb : linear p q ≠ 0 := (coefficient_nontrivial hpq).resolve_left (not_ne_iff.mpr ha)
  ext z
  change dist z p = dist z q ↔ z.re = -constant p q / linear p q
  rw [dist_eq_iff]
  simp only [form, ha, zero_mul, zero_add, UpperHalfPlane.coe_re]
  constructor
  · intro hz
    apply (eq_div_iff hb).mpr
    linarith
  · intro hz
    have h := (eq_div_iff hb).mp hz
    linarith

theorem bisector_semicircle {p q : ℍ} (ha : leading p q ≠ 0) :
    bisector p q = semicircle (center p q) (radius p q) := by
  have hpos := radiusSq_pos ha
  have hrsq : radius p q ^ 2 = radiusSq p q := Real.sq_sqrt hpos.le
  have hr : 0 ≤ radius p q := Real.sqrt_nonneg _
  ext z
  change dist z p = dist z q ↔ ‖(z : ℂ) - (center p q : ℂ)‖ = radius p q
  rw [dist_eq_iff, complete_square ha]
  constructor
  · intro hz
    have hn : Complex.normSq ((z : ℂ) - (center p q : ℂ)) = radiusSq p q :=
      sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)
    apply (sq_eq_sq₀ (norm_nonneg _) hr).mp
    rw [Complex.sq_norm, hn, hrsq]
  · intro hz
    rw [← Complex.sq_norm, hz, hrsq, sub_self, mul_zero]

theorem exists_shape {p q : ℍ} (hpq : p ≠ q) :
    (∃ c : ℝ, bisector p q = vertical c) ∨
      ∃ c r : ℝ, 0 < r ∧ bisector p q = semicircle c r := by
  by_cases ha : leading p q = 0
  · exact Or.inl ⟨_, bisector_vertical hpq ha⟩
  · exact Or.inr ⟨_, _, Real.sqrt_pos.mpr (radiusSq_pos ha), bisector_semicircle ha⟩

end VeechDichotomy.HyperbolicBisectorShapes
