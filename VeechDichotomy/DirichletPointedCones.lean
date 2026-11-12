module

public import VeechDichotomy.DirichletConeAngles

/-! A true Dirichlet corner has a pointed actual active cone: a vector
and its negative can satisfy both independent active normals only when
the vector is zero. The actual invertible tangent map preserves this
property, and a genuine nonzero center direction belongs to the cone. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletPointedCones

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletCorners HyperbolicDirichletInterior
open HyperbolicKleinMap HyperbolicKleinHalfPlanes DirichletActiveConstraints DirichletActiveCones
open HyperbolicDirectionVectors DirichletConeDirections KleinTangentEquivalence
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def Pointed (K : Set ℂ) : Prop := ∀ u : ℂ, u ∈ K → -u ∈ K → u = 0

theorem active_cone_pointed (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ corners Γ p) : Pointed (cone Γ p z) := by
  obtain ⟨_, γ, δ, hd, hI⟩ := hz
  intro u hu hneg
  have hlin (η : Γ) (hη : affineForm p (η • p) (point z) = 0) : linearPart p (η • p) u = 0 := by
    by_cases hfix : η • p = p
    · rw [hfix]
      simp [linearPart, HyperbolicBisectorNull.leading, HyperbolicBisectorNull.linear, HyperbolicBisectorNull.constant]
    · have hactive : η ∈ active Γ p z := ⟨hfix, (HyperbolicKleinHalfPlanes.dist_eq_iff p (η • p) z).mpr hη⟩
      have hp := hu η hactive
      have hn := hneg η hactive
      rw [map_neg] at hn
      linarith
  have hγ := hlin γ hI.1
  have hδ := hlin δ hI.2
  have hsub := affine_intersection_subsingleton 0 (normalRe p (γ • p)) (normalIm p (γ • p))
    0 (normalRe p (δ • p)) (normalIm p (δ • p)) hd
  apply hsub
  · constructor
    · simpa only [normalRe, normalIm, linearPart, add_apply, smul_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, smul_eq_mul, zero_add] using hγ
    · simpa only [normalRe, normalIm, linearPart, add_apply, smul_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, smul_eq_mul, zero_add] using hδ
  · simp

theorem physical_pointed (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ corners Γ p) : Pointed (physicalCone Γ p z) := by
  rintro u ⟨k, hk, rfl⟩ ⟨l, hl, he⟩
  have hkl : l = -k := by
    apply forward_injective z
    rw [map_neg]
    exact he
  have hkneg : -k ∈ cone Γ p z := hkl ▸ hl
  have hkzero := active_cone_pointed Γ p z hz k hk hkneg
  rw [hkzero, map_zero]

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem corner_ne_center (p z : ℍ) (hz : z ∈ corners Γ p) : z ≠ p := by
  intro he
  have hfront := corners_subset_frontier Γ p hz
  rw [he] at hfront
  exact (mem_frontier_iff_notMem_interior (center_mem Γ p)).mp hfront
    (DirichletInteriorDensity.center_interior Γ p)

theorem corner_nonzero_direction (p z : ℍ) (hz : z ∈ corners Γ p) :
    ∃ u : ℂ, u ∈ physicalCone Γ p z ∧ u ≠ 0 := by
  refine ⟨direction z p, direction_mem Γ p z p (center_mem Γ p), ?_⟩
  intro he
  exact corner_ne_center Γ p z hz ((direction_eq_zero_iff z p).mp he)

end VeechDichotomy.DirichletPointedCones
