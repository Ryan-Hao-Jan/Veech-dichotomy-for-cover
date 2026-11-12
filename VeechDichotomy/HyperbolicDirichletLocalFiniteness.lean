module

public import VeechDichotomy.HyperbolicDirichletRegions
public import Mathlib.Order.Filter.Finite

/-! Actual Dirichlet inequalities are locally a finite family for every
discrete SL2 subgroup. Proper discontinuity bounds the nearby centers;
triangle inequalities make every more distant constraint automatic.
Strict inequalities therefore give interior points, and every boundary
point lies on an actual bisector between two distinct orbit centers. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletLocalFiniteness

open LinearGroup HyperbolicDirichletRegions Set Filter Topology
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem finite_orbit_in_compact (p : ℍ) {K : Set ℍ} (hK : IsCompact K) :
    {γ : Γ | γ • p ∈ K}.Finite := by
  have hf : {γ : Γ | (((γ • ·) '' ({p} : Set ℍ)) ∩ K).Nonempty}.Finite :=
    finite_disjoint_inter_image isCompact_singleton hK
  exact hf.subset (fun γ hγ => ⟨γ • p, ⟨p, rfl, rfl⟩, hγ⟩)

def nearby (p z : ℍ) : Set Γ := {γ | γ • p ∈ Metric.closedBall z (dist z p + 2)}

theorem nearby_finite (p z : ℍ) : (nearby Γ p z).Finite :=
  finite_orbit_in_compact Γ p (isCompact_closedBall _ _)

omit [DiscreteTopology Γ] in
theorem region_iff_nearby (p z : ℍ) {w : ℍ} (hw : w ∈ Metric.ball z (1 / 2 : ℝ)) :
    w ∈ region Γ p ↔ ∀ γ ∈ nearby Γ p z, dist w p ≤ dist w (γ • p) := by
  constructor
  · intro h γ _
    exact h γ
  · intro h γ
    by_cases hnear : γ ∈ nearby Γ p z
    · exact h γ hnear
    · change ¬ dist (γ • p) z ≤ dist z p + 2 at hnear
      have hfar : dist z p + 2 < dist z (γ • p) := by
        simpa only [dist_comm] using lt_of_not_ge hnear
      have hwz : dist w z < (1 / 2 : ℝ) := Metric.mem_ball.mp hw
      have hwp := dist_triangle w z p
      have hzp := dist_triangle z w (γ • p)
      rw [dist_comm z w] at hzp
      linarith

theorem mem_interior_of_strict (p z : ℍ)
    (hstrict : ∀ γ : Γ, γ • p ≠ p → dist z p < dist z (γ • p)) : z ∈ interior (region Γ p) := by
  have hev : ∀ᶠ w in 𝓝 z, ∀ γ ∈ nearby Γ p z, dist w p ≤ dist w (γ • p) := by
    apply (nearby_finite Γ p z).eventually_all.mpr
    intro γ _
    by_cases hfix : γ • p = p
    · exact Eventually.of_forall (fun w => by rw [hfix])
    · have hg : ∀ᶠ w in 𝓝 z, dist w p < dist w (γ • p) :=
        (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)).mem_nhds (hstrict γ hfix)
      exact hg.mono (fun _ hw => hw.le)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [Metric.ball_mem_nhds z (by norm_num : 0 < (1 / 2 : ℝ)), hev] with w hw hnear
  exact (region_iff_nearby Γ p z hw).mpr hnear

theorem frontier_mem_bisector (p : ℍ) {z : ℍ} (hz : z ∈ frontier (region Γ p)) :
    ∃ γ : Γ, γ • p ≠ p ∧ dist z p = dist z (γ • p) := by
  have hzD : z ∈ region Γ p := (isClosed_region Γ p).frontier_subset hz
  by_contra hnone
  apply (mem_frontier_iff_notMem_interior hzD).mp hz
  apply mem_interior_of_strict Γ p z
  intro γ hγ
  have hne : dist z p ≠ dist z (γ • p) := fun heq => hnone ⟨γ, hγ, heq⟩
  exact lt_of_le_of_ne (hzD γ) hne

end VeechDichotomy.HyperbolicDirichletLocalFiniteness
