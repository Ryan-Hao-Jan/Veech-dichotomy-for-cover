module

public import VeechDichotomy.NativeCuspEscapeCover
public import VeechDichotomy.NativeCuspTailContainment

/-! An actual continuous path escaping the actual right native
lattice quotient eventually stays in one genuine parabolic horoball
after inverse hyperbolic projection. All cusp-cover hypotheses are
discharged by the actual compact-core theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeEscapingPathHoroball

open LinearGroup Set Filter Topology HyperbolicRegularCenters NativeFiniteCuspCharts
open NativeLatticeConjugation
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem exists_tail_horoball (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (g : ℝ → SL2) (hg : Continuous g)
    (hescape : Tendsto (fun t => (QuotientGroup.mk (g t) : SL2 ⧸ Γ)) atTop (cocompact (SL2 ⧸ Γ))) :
    ∃ (B : SL2) (τ ε : ℝ) (γ : Γ) (T : ℝ), 0 < τ ∧ IdealInfinityStabilizers.upper τ ∈ conjugate Γ B ∧
      0 < ε ∧ ∀ t : ℝ, T ≤ t → ε < (B • (γ⁻¹ • ((g t)⁻¹ • UpperHalfPlane.I))).im := by
  obtain ⟨R, hR, _, hpair⟩ := NativeCompatibleHoroballs.exists_compatible_depth Γ hΓ p hp
  obtain ⟨T, hT⟩ := eventually_atTop.mp (NativeCuspEscapeCover.eventually_covered Γ hΓ p hp R g hescape)
  have hf : Continuous (fun t : ℝ => (g t)⁻¹ • UpperHalfPlane.I) := hg.inv.smul continuous_const
  obtain ⟨u, γ, htail⟩ := NativeCuspTailContainment.tail_contained Γ hΓ p hp R hpair _ hf T hT
  let c := chart Γ hΓ p hp u
  refine ⟨c.matrix, c.period, R * (c.matrix • p).im, γ, T, c.period_pos, c.period_mem,
    mul_pos hR (c.matrix • p).im_pos, ?_⟩
  intro t ht
  obtain ⟨z, hz, he⟩ := htail t ht
  change γ • z = (g t)⁻¹ • UpperHalfPlane.I at he
  have hpoint : γ⁻¹ • ((g t)⁻¹ • UpperHalfPlane.I) = z := by rw [← he, inv_smul_smul]
  rw [hpoint]
  exact hz

end VeechDichotomy.NativeEscapingPathHoroball
