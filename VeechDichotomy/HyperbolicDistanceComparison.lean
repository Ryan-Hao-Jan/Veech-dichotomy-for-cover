module

public import VeechDichotomy.HyperbolicBisectorNull
public import VeechDichotomy.HyperbolicDirichletRegions

/-! Exact polynomial signs characterize genuine hyperbolic distance
comparisons. The difference of cosh-distances is the actual circle/line
form divided by a strictly positive denominator. Thus the real metric
Dirichlet constraints are actual geometric half-plane constraints. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDistanceComparison

open HyperbolicBisectorNull LinearGroup Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def form (p q : ℍ) (z : ℂ) : ℝ := leading p q * Complex.normSq z + linear p q * z.re + constant p q

theorem difference_eq (p q z : ℍ) :
    Real.cosh (dist z p) - Real.cosh (dist z q) = form p q z / (2 * z.im * p.im * q.im) := by
  rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist]
  dsimp only [form, leading, linear, constant]
  simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp [z.im_ne_zero, p.im_ne_zero, q.im_ne_zero]
  ring

theorem cosh_compare (p q z : ℍ) :
    Real.cosh (dist z p) ≤ Real.cosh (dist z q) ↔ dist z p ≤ dist z q := by
  simpa only [abs_of_nonneg dist_nonneg] using (Real.cosh_le_cosh (x := dist z p) (y := dist z q))

theorem dist_le_iff (p q z : ℍ) : dist z p ≤ dist z q ↔ form p q z ≤ 0 := by
  calc
    dist z p ≤ dist z q ↔ Real.cosh (dist z p) ≤ Real.cosh (dist z q) := (cosh_compare p q z).symm
    _ ↔ Real.cosh (dist z p) - Real.cosh (dist z q) ≤ 0 := sub_nonpos.symm
    _ ↔ form p q z ≤ 0 := by rw [difference_eq, div_le_iff₀ (by positivity), zero_mul]

theorem dist_lt_iff (p q z : ℍ) : dist z p < dist z q ↔ form p q z < 0 := by
  have hc : Real.cosh (dist z p) < Real.cosh (dist z q) ↔ dist z p < dist z q := by
    simpa only [abs_of_nonneg dist_nonneg] using (Real.cosh_lt_cosh (x := dist z p) (y := dist z q))
  calc
    dist z p < dist z q ↔ Real.cosh (dist z p) < Real.cosh (dist z q) := hc.symm
    _ ↔ Real.cosh (dist z p) - Real.cosh (dist z q) < 0 := sub_neg.symm
    _ ↔ form p q z < 0 := by rw [difference_eq, div_lt_iff₀ (by positivity), zero_mul]

theorem dist_eq_iff (p q z : ℍ) : dist z p = dist z q ↔ form p q z = 0 := by
  constructor
  · exact polynomial_eq_zero p q z
  · intro hz
    have hc : Real.cosh (dist z p) = Real.cosh (dist z q) := sub_eq_zero.mp (by rw [difference_eq, hz, zero_div])
    exact le_antisymm ((cosh_compare p q z).mp hc.le) ((cosh_compare q p z).mp hc.ge)

theorem region_polynomial (Γ : Subgroup SL2) (p : ℍ) :
    HyperbolicDirichletRegions.region Γ p = {z : ℍ | ∀ γ : Γ, form p (γ • p) z ≤ 0} := by
  ext z
  exact forall_congr' (fun γ => dist_le_iff p (γ • p) z)

end VeechDichotomy.HyperbolicDistanceComparison
