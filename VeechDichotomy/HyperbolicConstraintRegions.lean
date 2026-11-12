module

public import VeechDichotomy.DirichletCompactTruncations
public import Mathlib.Topology.Connected.Clopen

/-! Any collection of actual Dirichlet distance half-planes containing
all actual active constraints already defines the entire actual region.
Their intersection is connected in the actual Klein disk. The genuine
local active-constraint theorem makes the actual region both open and
closed in that intersection. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicConstraintRegions

open LinearGroup Set Filter Topology HyperbolicDirichletRegions HyperbolicKleinMap
open HyperbolicKleinHomeomorph HyperbolicKleinHalfPlanes DirichletActiveConstraints
open scoped UpperHalfPlane

def constraints (Γ : Subgroup SL2) (p : ℍ) (S : Set Γ) : Set ℍ :=
  {z | ∀ γ ∈ S, dist z p ≤ dist z (γ • p)}

theorem image_constraints (Γ : Subgroup SL2) (p : ℍ) (S : Set Γ) :
    point '' constraints Γ p S = Metric.ball 0 1 ∩ ⋂ γ : S, {u : ℂ | affineForm p (γ.val • p) u ≤ 0} := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one z, ?_⟩
    exact mem_iInter.mpr (fun γ => (HyperbolicKleinHalfPlanes.dist_le_iff p (γ.val • p) z).mp (hz γ.val γ.property))
  · intro u hu
    let v : Disk := ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu.1⟩
    let z := inverse v
    have heq : point z = u := congrArg Subtype.val (forward_inverse v)
    refine ⟨z, ?_, heq⟩
    intro γ hγ
    apply (HyperbolicKleinHalfPlanes.dist_le_iff p (γ • p) z).mpr
    rw [heq]
    exact mem_iInter.mp hu.2 ⟨γ, hγ⟩

theorem convex_image_constraints (Γ : Subgroup SL2) (p : ℍ) (S : Set Γ) :
    Convex ℝ (point '' constraints Γ p S) := by
  rw [image_constraints]
  exact (convex_ball _ _).inter (convex_iInter (fun γ => convex_halfPlane p (γ.val • p)))

theorem isPreconnected_constraints (Γ : Subgroup SL2) (p : ℍ) (S : Set Γ) :
    IsPreconnected (constraints Γ p S) :=
  DirichletCompactTruncations.point_isEmbedding.isInducing.isPreconnected_image.mp
    (convex_image_constraints Γ p S).isPreconnected

theorem eq_of_contains_active (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ) (S : Set Γ)
    (hS : ∀ z ∈ region Γ p, active Γ p z ⊆ S) : region Γ p = constraints Γ p S := by
  let P := constraints Γ p S
  let R : Set P := (Subtype.val : P → ℍ) ⁻¹' region Γ p
  let : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp (isPreconnected_constraints Γ p S)
  have hclosed : IsClosed R := (isClosed_region Γ p).preimage continuous_subtype_val
  have hopen : IsOpen R := by
    apply isOpen_iff_eventually.mpr
    intro q hq
    change q.val ∈ region Γ p at hq
    have he := (continuous_subtype_val.continuousAt (x := q)).tendsto.eventually
      (eventually_active_iff Γ p q.val hq)
    filter_upwards [he] with r hr
    change r.val ∈ region Γ p
    exact hr.mpr (fun γ hγ => r.property γ (hS q.val hq hγ))
  have hnonempty : R.Nonempty := ⟨⟨p, fun γ _ => center_mem Γ p γ⟩, center_mem Γ p⟩
  have heq : R = univ := (show IsClopen R from ⟨hclosed, hopen⟩).eq_univ hnonempty
  apply Subset.antisymm
  · exact fun z hz γ _ => hz γ
  · intro z hz
    have hr : (⟨z, hz⟩ : P) ∈ R := by rw [heq]; exact mem_univ _
    exact hr

end VeechDichotomy.HyperbolicConstraintRegions
