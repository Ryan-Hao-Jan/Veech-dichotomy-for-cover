module

public import VeechDichotomy.NativeDirichletFinitePresentation
public import VeechDichotomy.DirichletIdealInfinity
public import VeechDichotomy.HyperbolicBisectorShapes

/-! Above an actual finite height, a regular-center native lattice
Dirichlet region with ideal endpoint infinity is defined entirely by
its finitely many actual vertical bisectors. All other actual distance
constraints become automatic outside their bounded circles. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletUpperEndConstraints

open LinearGroup NativeVeech Set HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicBisectorNull HyperbolicDistanceComparison HyperbolicBisectorShapes
open DirichletIdealRadialPoints DirichletIdealInfinity
open scoped UpperHalfPlane

theorem high_circle_constraint (p q z : ℍ) (ha : leading p q < 0) (hy : radius p q ≤ z.im) :
    dist z p ≤ dist z q := by
  apply (HyperbolicDistanceComparison.dist_le_iff p q z).mpr
  rw [complete_square ha.ne]
  have hs : radius p q ^ 2 = radiusSq p q := Real.sq_sqrt (radiusSq_pos ha.ne).le
  have hsq : radius p q ^ 2 ≤ z.im ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) z.im_pos.le).mpr hy
  have hn : 0 ≤ Complex.normSq ((z : ℂ) - (center p q : ℂ)) - radiusSq p q := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero]
    nlinarith only [hs, hsq, sq_nonneg (z.re - center p q)]
  exact mul_nonpos_of_nonpos_of_nonneg ha.le hn

theorem exists_upper_constraints (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (hI : Complex.I ∈ idealBoundary Γ p) :
    ∃ (S : Finset Γ) (H : ℝ), 0 < H ∧ ∀ z : ℍ, H ≤ z.im →
      (z ∈ region Γ p ↔ ∀ γ ∈ S, leading p (γ • p) = 0 → linear p (γ • p) * z.re + constant p (γ • p) ≤ 0) := by
  classical
  obtain ⟨S, hS⟩ := NativeDirichletFinitePresentation.exists_finite_constraints Γ hΓ p hp
  let H : ℝ := 1 + ∑ γ ∈ S, radius p (γ • p)
  have hsum : 0 ≤ ∑ γ ∈ S, radius p (γ • p) := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hH : 0 < H := by dsimp only [H]; linarith only [hsum]
  have hrad (γ : Γ) (hγ : γ ∈ S) : radius p (γ • p) ≤ H := by
    have hle : radius p (γ • p) ≤ ∑ η ∈ S, radius p (η • p) :=
      Finset.single_le_sum (f := fun η => radius p (η • p)) (fun _ _ => Real.sqrt_nonneg _) hγ
    dsimp only [H]
    linarith only [hle]
  refine ⟨S, H, hH, ?_⟩
  intro z hz
  rw [hS]
  change (∀ γ ∈ S, dist z p ≤ dist z (γ • p)) ↔ _
  constructor
  · intro h γ hγ he
    have hf := (HyperbolicDistanceComparison.dist_le_iff p (γ • p) z).mp (h γ hγ)
    simpa only [form, he, zero_mul, zero_add, UpperHalfPlane.coe_re] using hf
  · intro h γ hγ
    have hlead : leading p (γ • p) ≤ 0 := sub_nonpos.mpr (orbit_height_le Γ p hI γ)
    rcases lt_or_eq_of_le hlead with ha | he
    · exact high_circle_constraint p (γ • p) z ha ((hrad γ hγ).trans hz)
    · apply (HyperbolicDistanceComparison.dist_le_iff p (γ • p) z).mpr
      simpa only [form, he, zero_mul, zero_add, UpperHalfPlane.coe_re] using h γ hγ he

end VeechDichotomy.DirichletUpperEndConstraints
