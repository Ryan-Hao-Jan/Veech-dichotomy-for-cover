module

public import VeechDichotomy.ClosedConeAngleMaximum

/-! The genuine angular width of every actual Dirichlet corner is
attained by actual region points and is strictly below pi. Actual local
cone realization, closed pointed cone compactness and positive endpoint
direction factors discharge the geometric supremum statements. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletCornerWidth

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletCorners HyperbolicIntrinsicAngles
open DirichletConeDirections DirichletConeAngles DirichletPointedCones DirichletCornerAngles
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem width_lt_pi (p z : ℍ) (hz : z ∈ corners Γ p) : width Γ p z < Real.pi := by
  rw [width_eq Γ p z hz.1]
  exact ClosedConeAngleMaximum.width_lt_pi (physical_isClosed Γ p z)
    (fun _ hu _ ht => physical_smul_mem Γ p z hu ht) (corner_nonzero_direction Γ p z hz)
    (physical_pointed Γ p z hz)

theorem deficit_pos (p z : ℍ) (hz : z ∈ corners Γ p) : 0 < deficit Γ p z :=
  sub_pos.mpr (width_lt_pi Γ p z hz)

theorem width_attained (p z : ℍ) (hz : z ∈ corners Γ p) :
    ∃ a b : ℍ, a ∈ region Γ p ∧ b ∈ region Γ p ∧ a ≠ z ∧ b ≠ z ∧ width Γ p z = angleAt z a b := by
  obtain ⟨u, v, hu, hv, hmax⟩ := ClosedConeAngleMaximum.maximum (physical_isClosed Γ p z)
    (fun _ hu _ ht => physical_smul_mem Γ p z hu ht) (corner_nonzero_direction Γ p z hz)
  obtain ⟨a, b, ha, hb, haz, hbz, hang⟩ := angle_realized Γ p z hz.1 hu.1 hv.1
    (ClosedConeAngleMaximum.unit_ne_zero hu) (ClosedConeAngleMaximum.unit_ne_zero hv)
  refine ⟨a, b, ha, hb, haz, hbz, ?_⟩
  rw [width_eq Γ p z hz.1, hmax, hang]

end VeechDichotomy.DirichletCornerWidth
