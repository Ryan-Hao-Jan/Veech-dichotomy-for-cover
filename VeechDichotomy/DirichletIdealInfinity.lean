module

public import VeechDichotomy.DirichletClosedHalfPlanes

/-! The ideal point at physical infinity belongs to the actual
Dirichlet closure exactly when the center has maximal height in its
actual group orbit. In that case the entire upward vertical ray from
the center lies in the actual region. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletIdealInfinity

open LinearGroup Set HyperbolicDirichletRegions HyperbolicKleinHalfPlanes
open HyperbolicBisectorNull HyperbolicDistanceComparison DirichletIdealRadialPoints
open scoped UpperHalfPlane

theorem affineForm_I (p q : ℍ) : affineForm p q Complex.I = q.im - p.im := by
  simp only [affineForm, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
  unfold leading
  ring

theorem mem_ideal_iff (Γ : Subgroup SL2) (p : ℍ) :
    Complex.I ∈ idealBoundary Γ p ↔ ∀ γ : Γ, (γ • p).im ≤ p.im := by
  rw [DirichletClosedHalfPlanes.idealBoundary_iff]
  simp only [Complex.norm_I, true_and, affineForm_I, sub_nonpos]

theorem orbit_height_le (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p) (γ : Γ) :
    (γ • p).im ≤ p.im := (mem_ideal_iff Γ p).mp hI γ

def verticalPoint (p : ℍ) (y : ℝ) (hy : 0 < y) : ℍ := ⟨⟨p.re, y⟩, hy⟩

theorem form_verticalPoint (p q : ℍ) (y : ℝ) (hy : 0 < y) :
    form p q (verticalPoint p y hy : ℂ) =
      form p q (p : ℂ) + (q.im - p.im) * (y ^ 2 - p.im ^ 2) := by
  simp only [form, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, verticalPoint, leading]
  ring

theorem verticalPoint_mem (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (y : ℝ) (hy : p.im ≤ y) : verticalPoint p y (p.im_pos.trans_le hy) ∈ region Γ p := by
  intro γ
  apply (HyperbolicDistanceComparison.dist_le_iff p (γ • p) _).mpr
  rw [form_verticalPoint]
  have hp := (HyperbolicDistanceComparison.dist_le_iff p (γ • p) p).mp (center_mem Γ p γ)
  have hlead : (γ • p).im - p.im ≤ 0 := sub_nonpos.mpr (orbit_height_le Γ p hI γ)
  have hs : 0 ≤ y ^ 2 - p.im ^ 2 := by nlinarith only [hy, p.im_pos]
  exact add_nonpos hp (mul_nonpos_of_nonpos_of_nonneg hlead hs)

end VeechDichotomy.DirichletIdealInfinity
