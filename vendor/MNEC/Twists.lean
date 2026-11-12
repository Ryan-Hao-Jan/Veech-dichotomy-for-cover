module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
The coordinate identities used in MNEC.tex, equations (twist-w),
(twist-L1), (twist-L2) and (area-change).

These are statements about vectors and determinants. They do not assert
that the new bases describe embedded subsurfaces of a translation surface.
That geometric admissibility theorem is a separate proof obligation.
-/

namespace MNEC
namespace Twists

abbrev Plane := ℝ × ℝ

def cross (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

def slit (w v₁ v₂ : Plane) (t : ℝ) : Plane :=
  (w.1 + t * (v₁.1 + v₂.1), w.2 + t * (v₁.2 + v₂.2))

def partner (b v : Plane) (t : ℝ) : Plane :=
  (b.1 + t * v.1, b.2 + t * v.2)

theorem first_transverse (w v₁ v₂ : Plane) (t : ℝ) :
    cross v₁ (slit w v₁ v₂ t) = cross v₁ w + t * cross v₁ v₂ := by
  simp only [cross, slit]
  ring

theorem second_transverse (w v₁ v₂ : Plane) (t : ℝ) :
    cross v₂ (slit w v₁ v₂ t) = cross v₂ w - t * cross v₁ v₂ := by
  simp only [cross, slit]
  ring

theorem first_area (v₁ b₁ v₂ : Plane) (t : ℝ) :
    cross v₁ (partner b₁ v₂ t) = cross v₁ b₁ + t * cross v₁ v₂ := by
  simp only [cross, partner]
  ring

theorem second_area (v₂ b₂ v₁ : Plane) (t : ℝ) :
    cross v₂ (partner b₂ v₁ t) = cross v₂ b₂ - t * cross v₁ v₂ := by
  simp only [cross, partner]
  ring

theorem total_area (v₁ b₁ v₂ b₂ : Plane) (t : ℝ) :
    cross v₁ (partner b₁ v₂ t) + cross v₂ (partner b₂ v₁ t) =
      cross v₁ b₁ + cross v₂ b₂ := by
  rw [first_area, second_area]
  ring

theorem sibling_determinant (w v₁ v₂ : Plane) (s t : ℝ) :
    cross (slit w v₁ v₂ t) (slit w v₁ v₂ s) =
      (s - t) * (cross w v₁ + cross w v₂) := by
  simp only [cross, slit]
  ring

theorem siblings_distinct (w v₁ v₂ : Plane) (s t : ℝ)
    (hst : s ≠ t) (h₁ : 0 < cross v₁ w) (h₂ : 0 < cross v₂ w) :
    cross (slit w v₁ v₂ t) (slit w v₁ v₂ s) ≠ 0 := by
  rw [sibling_determinant]
  apply mul_ne_zero (sub_ne_zero.mpr hst)
  have h : cross w v₁ + cross w v₂ = -(cross v₁ w + cross v₂ w) := by
    simp only [cross]
    ring
  rw [h]
  exact neg_ne_zero.mpr (ne_of_gt (add_pos h₁ h₂))

/-- The strict transverse bounds used to admit all sixteen twists.
The conclusion is the algebraic sign condition, not geometric existence. -/
theorem positive_transverse_of_small_twist (w v₁ v₂ : Plane) (t : ℝ)
    (h₁ : |t * cross v₁ v₂| < cross v₁ w)
    (h₂ : |t * cross v₁ v₂| < cross v₂ w) :
    0 < cross v₁ (slit w v₁ v₂ t) ∧
      0 < cross v₂ (slit w v₁ v₂ t) := by
  rw [first_transverse, second_transverse]
  have hlo := neg_abs_le (t * cross v₁ v₂)
  have hhi := le_abs_self (t * cross v₁ v₂)
  constructor <;> linarith

end Twists
end MNEC
