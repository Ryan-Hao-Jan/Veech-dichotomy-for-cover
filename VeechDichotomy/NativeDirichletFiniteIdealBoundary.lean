module

public import VeechDichotomy.DirichletIdealAreaBudget

/-! The actual ideal boundary of every finite-area Dirichlet region is
finite. In particular this holds for every center of an actual native
SL2 lattice. Together with the true-corner theorem this gives finitely
many actual and ideal vertices at a regular center. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDirichletFiniteIdealBoundary

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions
open HyperbolicDirichletCorners HyperbolicRegularCenters DirichletIdealRadialPoints
open scoped UpperHalfPlane ENNReal

theorem finite_of_area (Γ : Subgroup SL2) (p : ℍ) (hfinite : volume (region Γ p) ≠ ⊤) :
    (idealBoundary Γ p).Finite := by
  classical
  by_contra hinf
  have hi : (idealBoundary Γ p \ {Complex.I}).Infinite :=
    (show (idealBoundary Γ p).Infinite from hinf).sdiff (finite_singleton Complex.I)
  let B : ℝ := (volume (region Γ p)).toReal + 2 * Real.pi
  obtain ⟨n, hn⟩ := exists_nat_gt (B / Real.pi)
  obtain ⟨S, hS, hc⟩ := hi.exists_subset_card_eq (n + 3)
  have hmem (u : ℂ) (hu : u ∈ S) : u ∈ idealBoundary Γ p ∧ u ≠ Complex.I := by
    have h := hS hu
    exact ⟨h.1, by simpa only [mem_singleton_iff] using h.2⟩
  have hb := DirichletIdealAreaBudget.finite_family_bound Γ p hfinite S hmem (by omega)
  rw [hc, Nat.cast_add, Nat.cast_ofNat] at hb
  have hlarge : B < (n : ℝ) * Real.pi := (div_lt_iff₀ Real.pi_pos).mp hn
  have hpi := Real.pi_pos
  change ((n : ℝ) + 3) * Real.pi ≤ B at hb
  nlinarith only [hb, hlarge, hpi]

theorem idealBoundary_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) :
    (idealBoundary Γ p).Finite :=
  finite_of_area Γ p (NativeLatticeDirichletArea.area_lt_top Γ hΓ p).ne

theorem exists_regular_finite_vertices (Γ : Subgroup SL2) (hΓ : IsLattice Γ) :
    ∃ p : ℍ, RegularCenter Γ p ∧ (corners Γ p).Finite ∧ (idealBoundary Γ p).Finite ∧
      MeasurableSet (region Γ p) ∧ 0 < volume (region Γ p) ∧ volume (region Γ p) < ∞ ∧
      volume (frontier (region Γ p)) = 0 := by
  obtain ⟨p, hp, hc, hm, hpos, hfin, hnull⟩ := NativeDirichletFiniteCorners.exists_regular_finite_corners Γ hΓ
  exact ⟨p, hp, hc, idealBoundary_finite Γ hΓ p, hm, hpos, hfin, hnull⟩

end VeechDichotomy.NativeDirichletFiniteIdealBoundary
