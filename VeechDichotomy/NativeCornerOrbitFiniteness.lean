module

public import VeechDichotomy.DirichletCornerOrbitCycles

/-! There are only finitely many actual congruence classes meeting
the true corners of a regular-center native lattice Dirichlet region.
Actual disjoint finite cycles consume at least pi/3 each from the proved
finite-area deficit budget. An actual arbitrarily large finite family
would contradict that bound. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCornerOrbitFiniteness

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions HyperbolicRegularCenters
open DirichletCornerAngles DirichletCornerOrbitCycles
open scoped UpperHalfPlane ENNReal

theorem family_mass_bound (Γ : Subgroup SL2) [DiscreteTopology Γ] (hΓ : IsLattice Γ) (p : ℍ)
    (F : Finset (cornerClasses Γ p)) :
    (∑ q ∈ F, mass Γ p q) ≤ (volume (region Γ p)).toReal + 2 * Real.pi := by
  classical
  let T := F.biUnion (cycleFinset Γ p)
  have hT : ∀ w ∈ T, w ∈ region Γ p := by
    intro w hw
    obtain ⟨q, _, hwq⟩ := Finset.mem_biUnion.mp hw
    exact cycle_mem_region Γ p q hwq
  have hdisj : (F : Set (cornerClasses Γ p)).PairwiseDisjoint (cycleFinset Γ p) := by
    intro q _ r _ hqr
    exact cycles_disjoint Γ p hqr
  have hsum : (∑ w ∈ T, deficit Γ p w) = ∑ q ∈ F, mass Γ p q := Finset.sum_biUnion hdisj
  rw [← hsum]
  exact DirichletRegionDeficitBudgets.sum_deficit_bound Γ hΓ p T hT

theorem family_card_bound (Γ : Subgroup SL2) [DiscreteTopology Γ] (hΓ : IsLattice Γ) (p : ℍ)
    (hp : RegularCenter Γ p) (F : Finset (cornerClasses Γ p)) :
    (F.card : ℝ) * (Real.pi / 3) ≤ (volume (region Γ p)).toReal + 2 * Real.pi := by
  have hl : (F.card : ℝ) * (Real.pi / 3) ≤ ∑ q ∈ F, mass Γ p q := by
    calc
      _ = ∑ _q ∈ F, Real.pi / 3 := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun q _ => mass_ge_pi_div_three Γ p hp q)
  exact hl.trans (family_mass_bound Γ hΓ p F)

theorem cornerClasses_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    (cornerClasses Γ p).Finite := by
  let : DiscreteTopology Γ := hΓ.1
  classical
  by_contra hnot
  have hinf : (cornerClasses Γ p).Infinite := hnot
  let : Infinite (cornerClasses Γ p) := Set.infinite_coe_iff.mpr hinf
  let B : ℝ := (volume (region Γ p)).toReal + 2 * Real.pi
  obtain ⟨n, hn⟩ := exists_nat_gt (B / (Real.pi / 3))
  obtain ⟨F, hF⟩ := Finset.exists_card_eq (α := cornerClasses Γ p) n
  have hbound := family_card_bound Γ hΓ p hp F
  rw [hF] at hbound
  have hlarge : B < (n : ℝ) * (Real.pi / 3) := (div_lt_iff₀ (by positivity : 0 < Real.pi / 3)).mp hn
  exact not_lt_of_ge hbound hlarge

end VeechDichotomy.NativeCornerOrbitFiniteness
