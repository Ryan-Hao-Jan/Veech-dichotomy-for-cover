module

public import VeechDichotomy.SL2HyperbolicCoordinates
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Actual closed Dirichlet regions for arbitrary discrete SL2 subgroups
acting on the genuine hyperbolic upper half-plane. Properness makes each
orbit closed; a nearest orbit point exists in the proper hyperbolic
metric. Moving it to the center proves the translates cover the plane.
No finite-area polygon or cusp theorem is assumed here. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletRegions

open LinearGroup Set Topology
open scoped UpperHalfPlane Pointwise

variable (Γ : Subgroup SL2)

def region (p : ℍ) : Set ℍ := {z | ∀ γ : Γ, dist z p ≤ dist z (γ • p)}

theorem isClosed_region (p : ℍ) : IsClosed (region Γ p) := by
  have heq : region Γ p = ⋂ γ : Γ, {z : ℍ | dist z p ≤ dist z (γ • p)} := by
    ext z
    simp [region]
  rw [heq]
  exact isClosed_iInter (fun _ => isClosed_le (continuous_id.dist continuous_const)
    (continuous_id.dist continuous_const))

theorem center_mem (p : ℍ) : p ∈ region Γ p := fun _ => by simp

variable [DiscreteTopology Γ]

theorem orbit_closed (p : ℍ) : IsClosed (MulAction.orbit Γ p) := by
  let : IsClosed (Γ : Set SL2) := Subgroup.isClosed_of_discreteTopology
  have hp : IsClosed ((univ : Set Γ) • ({p} : Set ℍ)) :=
    isClosed_univ.smul_right_of_isCompact isCompact_singleton
  simpa only [Set.smul_singleton, Set.image_univ, MulAction.orbit] using hp

theorem exists_nearest (p z : ℍ) : ∃ γ : Γ, ∀ δ : Γ, dist z (γ • p) ≤ dist z (δ • p) := by
  have hne : (MulAction.orbit Γ p).Nonempty := ⟨p, 1, one_smul Γ p⟩
  obtain ⟨w, hw, hd⟩ := (orbit_closed Γ p).exists_infDist_eq_dist hne z
  obtain ⟨γ, rfl⟩ := hw
  refine ⟨γ, fun δ => ?_⟩
  rw [← hd]
  exact Metric.infDist_le_dist_of_mem (MulAction.mem_orbit p δ)

theorem exists_translate_mem (p z : ℍ) : ∃ γ : Γ, γ • z ∈ region Γ p := by
  obtain ⟨γ, hmin⟩ := exists_nearest Γ p z
  refine ⟨γ⁻¹, fun δ => ?_⟩
  change dist ((γ : SL2)⁻¹ • z) p ≤ dist ((γ : SL2)⁻¹ • z) ((δ : SL2) • p)
  have hl := dist_smul ((γ : SL2)⁻¹) z ((γ : SL2) • p)
  have hr := dist_smul ((γ : SL2)⁻¹) z ((γ : SL2) • ((δ : SL2) • p))
  simp only [inv_smul_smul] at hl hr
  rw [hl, hr]
  simpa only [Subgroup.coe_mul, mul_smul] using! hmin (γ * δ)

end VeechDichotomy.HyperbolicDirichletRegions
