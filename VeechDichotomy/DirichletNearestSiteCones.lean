module

public import VeechDichotomy.DirichletSiteNormals

/-! The genuine local physical Dirichlet cone is the normal cone of
the actual finite set of nearest-site vectors. Those vectors are distinct
and lie on one actual circle; at a boundary point there are at least two.
All centers, vector identities and cone signs are proved from the actual
group orbit and actual Poincare metric, without a Voronoi interface. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletNearestSiteCones

open LinearGroup Set HyperbolicDirichletRegions HyperbolicDirichletCorners DirichletTileCenters
open HyperbolicNearestSiteVectors DirichletSiteNormals DirichletActiveConstraints
open DirichletConeDirections DirichletActiveCones KleinTangentEquivalence
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def sites (Γ : Subgroup SL2) (p z : ℍ) : Set ℂ := site z '' centersAt Γ p z

def normalCone (Γ : Subgroup SL2) (p z : ℍ) : Set ℂ :=
  {u | ∀ s ∈ sites Γ p z, inner ℝ (s - site z p) u ≤ 0}

theorem sites_finite (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ) : (sites Γ p z).Finite :=
  (centersAt_finite Γ p z).image (site z)

theorem base_site_mem (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ region Γ p) : site z p ∈ sites Γ p z :=
  ⟨p, ⟨⟨1, one_smul Γ p⟩, hz⟩, rfl⟩

theorem sites_on_circle (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ region Γ p) :
    ∀ u ∈ sites Γ p z, ‖u‖ = Real.sinh (dist z p) := by
  rintro u ⟨q, hq, rfl⟩
  rw [site_norm, ((centersAt_iff_equal_distance Γ p z hz q).mp hq).2]

theorem site_injective (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ region Γ p) :
    InjOn (site z) (centersAt Γ p z) := by
  intro q hq r hr he
  have hdq := ((centersAt_iff_equal_distance Γ p z hz q).mp hq).2
  have hdr := ((centersAt_iff_equal_distance Γ p z hz r).mp hr).2
  exact site_injective_on_circle z q r (hdq.trans hdr.symm) he

theorem physicalCone_eq_normalCone (Γ : Subgroup SL2) (p z : ℍ) (hz : z ∈ region Γ p) :
    physicalCone Γ p z = normalCone Γ p z := by
  apply Subset.antisymm
  · rintro u ⟨k, hk, rfl⟩ s ⟨q, hq, rfl⟩
    by_cases heqp : q = p
    · rw [heqp, sub_self, inner_zero_left]
    obtain ⟨γ, hγ⟩ := hq.1
    change γ • p = q at hγ
    have hd : dist z p = dist z q := ((centersAt_iff_equal_distance Γ p z hz q).mp hq).2.symm
    have hactive : γ ∈ active Γ p z := ⟨by rwa [hγ], by rwa [hγ]⟩
    have hL := hk γ hactive
    rw [hγ, active_normal_identity p q z hd k] at hL
    have hm : (p.im * q.im) * inner ℝ (site z q - site z p) (forward z k) ≤ (p.im * q.im) * 0 := by
      simpa only [mul_zero] using hL
    exact (mul_le_mul_iff_of_pos_left (mul_pos p.im_pos q.im_pos)).mp hm
  · intro u hu
    refine ⟨inverse z u, ?_, forward_inverse z u⟩
    intro γ hγ
    have hq : γ • p ∈ centersAt Γ p z := (centersAt_iff_equal_distance Γ p z hz _).mpr
      ⟨MulAction.mem_orbit p γ, hγ.2.symm⟩
    have hs : site z (γ • p) ∈ sites Γ p z := ⟨γ • p, hq, rfl⟩
    have hinner := hu _ hs
    rw [active_normal_identity p (γ • p) z hγ.2 (inverse z u), forward_inverse]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_pos p.im_pos (γ • p).im_pos).le hinner

theorem boundary_radius_pos (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ)
    (hz : z ∈ frontier (region Γ p)) : 0 < Real.sinh (dist z p) := by
  have hne : z ≠ p := by
    intro he
    rw [he] at hz
    exact (mem_frontier_iff_notMem_interior (center_mem Γ p)).mp hz (DirichletInteriorDensity.center_interior Γ p)
  exact Real.sinh_pos_iff.mpr (dist_pos.mpr hne)

theorem boundary_other_site (Γ : Subgroup SL2) [DiscreteTopology Γ] (p z : ℍ)
    (hz : z ∈ frontier (region Γ p)) : ∃ u ∈ sites Γ p z, u ≠ site z p := by
  obtain ⟨γ, hγ⟩ := active_nonempty_of_frontier Γ p hz
  have hzD : z ∈ region Γ p := (isClosed_region Γ p).frontier_subset hz
  have hq : γ • p ∈ centersAt Γ p z := (centersAt_iff_equal_distance Γ p z hzD _).mpr
    ⟨MulAction.mem_orbit p γ, hγ.2.symm⟩
  refine ⟨site z (γ • p), ⟨γ • p, hq, rfl⟩, ?_⟩
  intro he
  exact hγ.1 (site_injective_on_circle z (γ • p) p hγ.2.symm he)

end VeechDichotomy.DirichletNearestSiteCones
