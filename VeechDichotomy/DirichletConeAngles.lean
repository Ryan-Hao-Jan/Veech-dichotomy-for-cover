module

public import VeechDichotomy.DirichletConeDirections

/-! The actual Dirichlet angular-width definition is exactly the
angular width of its genuine physical active cone. Both inclusions of
the entire angle-value sets are proved: actual endpoints give cone
directions, and every nonzero cone direction is actually realized. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletConeAngles

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirectionVectors HyperbolicIntrinsicAngles
open DirichletConeDirections HyperbolicRegionAngles
open scoped UpperHalfPlane

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem angle_realized (p z : ℍ) (hz : z ∈ region Γ p) {u v : ℂ}
    (hu : u ∈ physicalCone Γ p z) (hv : v ∈ physicalCone Γ p z) (hune : u ≠ 0) (hvne : v ≠ 0) :
    ∃ a b : ℍ, a ∈ region Γ p ∧ b ∈ region Γ p ∧ a ≠ z ∧ b ≠ z ∧
      angleAt z a b = InnerProductGeometry.angle u v := by
  obtain ⟨a, s, ha, haz, hs, hda⟩ := physical_direction_realized Γ p z hz hu hune
  obtain ⟨b, t, hb, hbz, ht, hdb⟩ := physical_direction_realized Γ p z hz hv hvne
  refine ⟨a, b, ha, hb, haz, hbz, ?_⟩
  rw [angleAt, hda, hdb, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]

theorem values_eq (p z : ℍ) (hz : z ∈ region Γ p) :
    DirichletCornerAngles.values Γ p z = vectorValues (physicalCone Γ p z) := by
  ext θ
  constructor
  · rintro (hzero | ⟨a, b, ha, hb, haz, hbz, hθ⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨direction z a, direction z b, direction_mem Γ p z a ha,
        direction_mem Γ p z b hb, ?_, ?_, hθ⟩
      · exact fun he => haz ((direction_eq_zero_iff z a).mp he).symm
      · exact fun he => hbz ((direction_eq_zero_iff z b).mp he).symm
  · rintro (hzero | ⟨u, v, hu, hv, hune, hvne, hθ⟩)
    · exact Or.inl hzero
    · obtain ⟨a, b, ha, hb, haz, hbz, hang⟩ := angle_realized Γ p z hz hu hv hune hvne
      exact Or.inr ⟨a, b, ha, hb, haz, hbz, hθ.trans hang.symm⟩

theorem width_eq (p z : ℍ) (hz : z ∈ region Γ p) :
    DirichletCornerAngles.width Γ p z = vectorWidth (physicalCone Γ p z) := by
  change sSup (DirichletCornerAngles.values Γ p z) = sSup (vectorValues (physicalCone Γ p z))
  rw [values_eq Γ p z hz]

end VeechDichotomy.DirichletConeAngles
