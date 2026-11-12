module

public import VeechDichotomy.NativeDirichletFinitePresentation
public import VeechDichotomy.DirichletClosedHalfPlanes

/-! A genuine finite presentation of a Dirichlet region also describes
its actual ideal boundary. The reverse boundary inclusion is proved
using actual radial points and the exact region equality. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletFiniteClosurePresentation

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicKleinHalfPlanes
open DirichletIdealRadialPoints IdealRadialLimits
open scoped UpperHalfPlane

theorem ideal_mem_of_constraints (Γ : Subgroup SL2) (p : ℍ) (S : Finset Γ)
    (hS : region Γ p = {z : ℍ | ∀ γ ∈ S, dist z p ≤ dist z (γ • p)})
    (u : ℂ) (hu : ‖u‖ = 1) (hhalf : ∀ γ ∈ S, affineForm p (γ • p) u ≤ 0) :
    u ∈ idealBoundary Γ p := by
  refine ⟨?_, hu⟩
  apply isClosed_closure.mem_of_tendsto (radial_tendsto p u)
  apply Eventually.of_forall
  intro k
  refine subset_closure ⟨approx p u hu k, ?_, point_approx p u hu k⟩
  rw [hS]
  intro γ hγ
  apply (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) _).mpr
  rw [point_approx]
  have hp := (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) p).mp (center_mem Γ p γ)
  exact (convex_halfPlane p (γ • p)) hp (hhalf γ hγ)
    (sub_nonneg.mpr (time_lt_one k).le) (time_pos k).le (by ring)

theorem idealBoundary_iff (Γ : Subgroup SL2) (p : ℍ) (S : Finset Γ)
    (hS : region Γ p = {z : ℍ | ∀ γ ∈ S, dist z p ≤ dist z (γ • p)}) (u : ℂ) :
    u ∈ idealBoundary Γ p ↔ ‖u‖ = 1 ∧ ∀ γ ∈ S, affineForm p (γ • p) u ≤ 0 := by
  constructor
  · exact fun hu => ⟨hu.2, fun γ _ => closure_halfPlane Γ p hu.1 γ⟩
  · exact fun hu => ideal_mem_of_constraints Γ p S hS u hu.1 hu.2

end VeechDichotomy.DirichletFiniteClosurePresentation
