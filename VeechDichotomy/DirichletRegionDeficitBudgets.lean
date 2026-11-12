module

public import VeechDichotomy.DirichletWidthPositive

/-! The actual finite-corner budget extends to every finite subset
of the actual Dirichlet region, since every noncorner has deficit zero.
In particular the entire actual finite congruence cycle, including any
flat boundary points, satisfies the same native lattice deficit bound. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletRegionDeficitBudgets

open LinearGroup NativeVeech Set MeasureTheory HyperbolicDirichletRegions HyperbolicDirichletCorners
open DirichletCornerAngles HyperbolicDirichletPointCycles
open scoped UpperHalfPlane ENNReal

theorem sum_deficit_bound (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (S : Finset ℍ)
    (hS : ∀ z ∈ S, z ∈ region Γ p) :
    (∑ z ∈ S, deficit Γ p z) ≤ (volume (region Γ p)).toReal + 2 * Real.pi := by
  let : DiscreteTopology Γ := hΓ.1
  classical
  let T := S.filter (fun z => z ∈ corners Γ p)
  have hsub : T ⊆ S := Finset.filter_subset _ _
  have hsum : (∑ z ∈ T, deficit Γ p z) = ∑ z ∈ S, deficit Γ p z := by
    apply Finset.sum_subset hsub
    intro z hz hnot
    have hnc : z ∉ corners Γ p := fun hc => hnot (Finset.mem_filter.mpr ⟨hz, hc⟩)
    exact DirichletNoncornerWidth.deficit_zero Γ p z (hS z hz) hnc
  rw [← hsum]
  exact NativeFiniteCornerDeficitBudget.sum_deficit_bound Γ hΓ p T (fun _ hz => (Finset.mem_filter.mp hz).2)

theorem finite_cycle_budget (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p z : ℍ) :
    ∃ C : Finset ℍ, (C : Set ℍ) = region Γ p ∩ MulAction.orbit Γ z ∧ C.Nonempty ∧
      (∑ w ∈ C, deficit Γ p w) ≤ (volume (region Γ p)).toReal + 2 * Real.pi := by
  let : DiscreteTopology Γ := hΓ.1
  classical
  let C := (cycle_finite Γ p z).toFinset
  have he : (C : Set ℍ) = region Γ p ∩ MulAction.orbit Γ z := (cycle_finite Γ p z).coe_toFinset
  have hC : ∀ w ∈ C, w ∈ region Γ p := by
    intro w hw
    have hm : w ∈ (C : Set ℍ) := hw
    rw [he] at hm
    exact hm.1
  obtain ⟨γ, hγ⟩ := exists_translate_mem Γ p z
  have hpoint : γ • z ∈ (C : Set ℍ) := by
    rw [he]
    exact ⟨hγ, MulAction.mem_orbit z γ⟩
  exact ⟨C, he, ⟨γ • z, hpoint⟩, sum_deficit_bound Γ hΓ p C hC⟩

end VeechDichotomy.DirichletRegionDeficitBudgets
