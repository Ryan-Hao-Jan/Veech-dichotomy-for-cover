module

public import VeechDichotomy.DirichletBoundaryCycles

/-! The actual discrete Dirichlet region and every actual tile are
closures of their interiors. Genuine Klein convexity, the actual open
coordinate embedding and the strict center prove this topological fact. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletInteriorDensity

open LinearGroup Set Topology HyperbolicDirichletRegions HyperbolicDirichletInterior
open HyperbolicKleinMap HyperbolicGeodesicHulls HyperbolicKleinDirichlet
open HyperbolicDirichletTessellation DirichletBoundaryCycles
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

variable (Γ : Subgroup SL2) [DiscreteTopology Γ]

theorem center_interior (p : ℍ) : p ∈ interior (region Γ p) := by
  apply HyperbolicDirichletLocalFiniteness.mem_interior_of_strict Γ p p
  intro γ hγ
  rw [dist_self]
  exact dist_pos.mpr hγ.symm

theorem closure_interior_region (p : ℍ) : closure (interior (region Γ p)) = region Γ p := by
  let S := point '' region Γ p
  have hS : (interior S).Nonempty := ⟨point p,
    point_isOpenMap.image_interior_subset _ ⟨p, center_interior Γ p, rfl⟩⟩
  have hconv : Convex ℝ S := convex_image_region Γ p
  have hc : closure (interior S) = closure S := hconv.closure_interior_eq_closure_of_nonempty_interior hS
  have hi : point ⁻¹' interior S = interior (region Γ p) := by
    rw [point_isOpenMap.preimage_interior_eq_interior_preimage continuous_point,
      preimage_image_eq _ point_injective]
  calc
    closure (interior (region Γ p)) = closure (point ⁻¹' interior S) := by rw [hi]
    _ = point ⁻¹' closure (interior S) :=
      (point_isOpenMap.preimage_closure_eq_closure_preimage continuous_point _).symm
    _ = point ⁻¹' closure S := by rw [hc]
    _ = closure (region Γ p) := (point_isEmbedding.closure_eq_preimage_closure_image _).symm
    _ = region Γ p := (isClosed_region Γ p).closure_eq

theorem closure_interior_tile (p : ℍ) (γ : Γ) : closure (interior (tile Γ p γ)) = tile Γ p γ := by
  rw [interior_tile, ← HyperbolicDirichletInterior.interior_eq_strict Γ p]
  change closure ((Homeomorph.smul γ : ℍ ≃ₜ ℍ) '' interior (region Γ p)) =
    (Homeomorph.smul γ : ℍ ≃ₜ ℍ) '' region Γ p
  rw [← (Homeomorph.smul γ : ℍ ≃ₜ ℍ).image_closure, closure_interior_region Γ p]

end VeechDichotomy.DirichletInteriorDensity
