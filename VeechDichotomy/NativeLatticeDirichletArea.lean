module

public import VeechDichotomy.HyperbolicDirichletNullBoundary
public import VeechDichotomy.FundamentalDomainMultiplicity
public import VeechDichotomy.NativeLatticeHyperbolicVolume

/-! Every ACTUAL native SL2 lattice has genuine Dirichlet regions of
positive finite hyperbolic area, with null frontier. Strict-region
overlaps are bounded by the actual finite stabilizer. The actual finite
geometric group domain gives a packing bound, and the exact projection
formula identifies the resulting mass with actual dxdy/y^2 area.
No finite-area, torsion-free, or generic-center assumption is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeDirichletArea

open LinearGroup NativeVeech NativeLatticeLeftVolume NativeLatticeHyperbolicVolume
open HyperbolicDirichletRegions HyperbolicStrictDirichlet HyperbolicDirichletNullBoundary
open SL2HyperbolicVolume Set MeasureTheory
open scoped UpperHalfPlane ENNReal

variable (Γ : Subgroup SL2) (hΓ : IsLattice Γ)
include hΓ

theorem strict_area_lt_top (p : ℍ) : volume (strictRegion Γ p) < ∞ := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  let T : Set SL2 := (fun g : SL2 => g • UpperHalfPlane.I) ⁻¹' strictRegion Γ p
  let S : Set Γ := {γ | γ • p = p}
  have hm : Measurable (fun g : SL2 => g • UpperHalfPlane.I) :=
    (continuous_id.smul continuous_const).measurable
  have hT : MeasurableSet T := hm (measurable_strictRegion Γ p)
  have hrel : ∀ x : SL2, ∀ g h : Γ, g • x ∈ T → h • x ∈ T → g * h⁻¹ ∈ S := by
    intro x g h hg hh
    change (g * h⁻¹) • p = p
    change ((g : SL2) * x) • UpperHalfPlane.I ∈ strictRegion Γ p at hg
    change ((h : SL2) * x) • UpperHalfPlane.I ∈ strictRegion Γ p at hh
    rw [mul_smul] at hg hh
    exact relative_fixes Γ p (x • UpperHalfPlane.I) g h hg hh
  have hvol : hyperbolicVolume T < ∞ := FundamentalDomainMultiplicity.measure_lt_top_of_relative
    hyperbolicVolume (NativeLatticeLeftVolume.isFundamentalDomain Γ hΓ hyperbolicVolume)
    (volume_domain_lt_top Γ hΓ) hT S (stabilizer_finite Γ p) hrel
  have heq : hyperbolicVolume T = volume (strictRegion Γ p) := projection_volume (measurable_strictRegion Γ p)
  rwa [heq] at hvol

theorem area_lt_top (p : ℍ) : volume (region Γ p) < ∞ := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  rw [volume_region_eq_strict Γ p]
  exact strict_area_lt_top Γ hΓ p

theorem area_pos (p : ℍ) : 0 < volume (region Γ p) := by
  let : DiscreteTopology Γ := hΓ.1
  have hint : p ∈ interior (region Γ p) :=
    HyperbolicDirichletLocalFiniteness.mem_interior_of_strict Γ p p (fun γ hγ => by
      rw [dist_self]
      exact dist_pos.mpr hγ.symm)
  exact Measure.measure_pos_of_nonempty_interior volume ⟨p, hint⟩

theorem frontier_area_zero (p : ℍ) : volume (frontier (region Γ p)) = 0 := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  exact HyperbolicDirichletNullBoundary.frontier_null Γ p

theorem dirichlet_region_finite_area (p : ℍ) : MeasurableSet (region Γ p) ∧
    0 < volume (region Γ p) ∧ volume (region Γ p) < ∞ ∧ volume (frontier (region Γ p)) = 0 :=
  ⟨(isClosed_region Γ p).measurableSet, area_pos Γ hΓ p, area_lt_top Γ hΓ p, frontier_area_zero Γ hΓ p⟩

end VeechDichotomy.NativeLatticeDirichletArea
