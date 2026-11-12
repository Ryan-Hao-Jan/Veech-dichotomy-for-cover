module

public import VeechDichotomy.DirichletVerticalEndBounds

/-! Actual opposite vertical distance constraints bound the entire
Dirichlet region between two genuine vertical lines, with the center
strictly between them. All endpoints and signs are literal coordinates. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletVerticalStripBounds

open LinearGroup Set HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicBisectorNull HyperbolicDistanceComparison DirichletIdealRadialPoints
open scoped UpperHalfPlane

def midpoint (p q : ℍ) : ℝ := (p.re + q.re) / 2

theorem linear_vertical (p q : ℍ) (ha : leading p q = 0) :
    linear p q = 2 * p.im * (q.re - p.re) := by
  have hh : q.im = p.im := sub_eq_zero.mp ha
  unfold linear
  rw [hh]
  ring

theorem vertical_factor (p q : ℍ) (ha : leading p q = 0) (x : ℝ) :
    linear p q * x + constant p q = linear p q * (x - midpoint p q) := by
  have hh : q.im = p.im := sub_eq_zero.mp ha
  unfold linear constant midpoint
  rw [hh]
  ring

theorem dist_le_vertical_iff (p q z : ℍ) (ha : leading p q = 0) :
    dist z p ≤ dist z q ↔ linear p q * (z.re - midpoint p q) ≤ 0 := by
  rw [HyperbolicDistanceComparison.dist_le_iff]
  simp only [form, ha, zero_mul, zero_add, UpperHalfPlane.coe_re, vertical_factor p q ha]

theorem midpoint_lt_center (p q : ℍ) (ha : leading p q = 0) (hb : linear p q < 0) :
    midpoint p q < p.re := by
  have hd : q.re < p.re := by
    by_contra hn
    have hp : 0 ≤ 2 * p.im * (q.re - p.re) :=
      mul_nonneg (mul_pos (by norm_num) p.im_pos).le (sub_nonneg.mpr (le_of_not_gt hn))
    rw [← linear_vertical p q ha] at hp
    exact not_le_of_gt hb hp
  unfold midpoint
  linarith only [hd]

theorem center_lt_midpoint (p q : ℍ) (ha : leading p q = 0) (hb : 0 < linear p q) :
    p.re < midpoint p q := by
  have hd : p.re < q.re := by
    by_contra hn
    have hp : 2 * p.im * (q.re - p.re) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos (by norm_num) p.im_pos).le (sub_nonpos.mpr (le_of_not_gt hn))
    rw [← linear_vertical p q ha] at hp
    exact not_le_of_gt hb hp
  unfold midpoint
  linarith only [hd]

theorem lower_bound (p q z : ℍ) (ha : leading p q = 0) (hb : linear p q < 0) (hz : dist z p ≤ dist z q) :
    midpoint p q ≤ z.re := by
  have h := (dist_le_vertical_iff p q z ha).mp hz
  by_contra hn
  have hpos := mul_pos_of_neg_of_neg hb (sub_neg.mpr (lt_of_not_ge hn))
  exact not_lt_of_ge h hpos

theorem upper_bound (p q z : ℍ) (ha : leading p q = 0) (hb : 0 < linear p q) (hz : dist z p ≤ dist z q) :
    z.re ≤ midpoint p q := by
  have h := (dist_le_vertical_iff p q z ha).mp hz
  have hm : linear p q * (z.re - midpoint p q) ≤ linear p q * 0 := by simpa only [mul_zero] using h
  exact sub_nonpos.mp ((mul_le_mul_iff_of_pos_left hb).mp hm)

theorem exists_bounds (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (hI : Complex.I ∈ idealBoundary Γ p) :
    ∃ a b : ℝ, a < p.re ∧ p.re < b ∧ ∀ z ∈ region Γ p, a ≤ z.re ∧ z.re ≤ b := by
  obtain ⟨γ, δ, hγa, hγb, hδa, hδb⟩ := DirichletVerticalEndBounds.exists_vertical_pair Γ hΓ p hp hI
  refine ⟨midpoint p (γ • p), midpoint p (δ • p), midpoint_lt_center p (γ • p) hγa hγb,
    center_lt_midpoint p (δ • p) hδa hδb, ?_⟩
  intro z hz
  exact ⟨lower_bound p (γ • p) z hγa hγb (hz γ), upper_bound p (δ • p) z hδa hδb (hz δ)⟩

end VeechDichotomy.DirichletVerticalStripBounds
