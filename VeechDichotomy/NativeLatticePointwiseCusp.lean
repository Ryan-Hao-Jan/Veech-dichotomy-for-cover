module

public import VeechDichotomy.NativeEscapingPathHoroball
public import VeechDichotomy.DiagonalHyperbolicRayLimits
public import VeechDichotomy.CuspRayMatrixNormalForm

/-! The actual pointwise cusp theorem for the actual native lattice
quotient: a specified escaping diagonal ray yields an actual nonzero
contracted lower unipotent conjugate in the group. Every geometric
and compact-core hypothesis is proved from the native lattice condition. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticePointwiseCusp

open LinearGroup Filter Topology HyperbolicRegularCenters NativeTeichmullerRay NativeShearMatrices
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem escaping_has_lower (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (A : SL2)
    (hescape : Tendsto (fun t => (QuotientGroup.mk (diagonal t * A) : SL2 ⧸ Γ)) atTop (cocompact (SL2 ⧸ Γ))) :
    ∃ s : ℝ, s ≠ 0 ∧ A⁻¹ * lower s * A ∈ Γ := by
  obtain ⟨p, hp, _, _, _, _⟩ := NativeLatticeRegularDirichlet.exists_regular_dirichlet Γ hΓ
  obtain ⟨B, τ, ε, γ, T, hτ, hperiod, hε, htail⟩ :=
    NativeEscapingPathHoroball.exists_tail_horoball Γ hΓ p hp (fun t => diagonal t * A)
      (continuous_diagonal.mul continuous_const) hescape
  let C : SL2 := B * (γ : SL2)⁻¹ * A⁻¹
  have hpoint (t : ℝ) : B • (γ⁻¹ • ((diagonal t * A)⁻¹ • UpperHalfPlane.I)) =
      C • DiagonalHyperbolicRayLimits.point t := by
    change B • ((γ : SL2)⁻¹ • ((diagonal t * A)⁻¹ • UpperHalfPlane.I)) = _
    dsimp only [C, DiagonalHyperbolicRayLimits.point]
    simp only [mul_inv_rev, SL2ParabolicRayEscape.diagonal_inverse, mul_smul]
  have hheight : ∀ᶠ t in atTop, ε < (C • DiagonalHyperbolicRayLimits.point t).im := by
    filter_upwards [eventually_ge_atTop T] with t ht
    rw [← hpoint]
    exact htail t ht
  have hd := DiagonalHyperbolicRayLimits.lower_right_zero_of_eventual_height C ε hε hheight
  let s := -(C 1 0 ^ 2) * τ
  refine ⟨s, CuspRayMatrixNormalForm.parameter_ne_zero C hd hτ.ne', ?_⟩
  have hnormal : C⁻¹ * IdealInfinityStabilizers.upper τ * C = lower s := CuspRayMatrixNormalForm.conjugate_upper C hd τ
  have hpΓ : B⁻¹ * IdealInfinityStabilizers.upper τ * B ∈ Γ := hperiod
  have hconj : (γ : SL2) * (B⁻¹ * IdealInfinityStabilizers.upper τ * B) * (γ : SL2)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem γ.property hpΓ) (Γ.inv_mem γ.property)
  have he : A⁻¹ * lower s * A = (γ : SL2) * (B⁻¹ * IdealInfinityStabilizers.upper τ * B) * (γ : SL2)⁻¹ := by
    rw [← hnormal]
    dsimp only [C]
    group
  rw [he]
  exact hconj

theorem divergent_iff_parabolic (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (A : SL2) :
    Tendsto (fun t => (QuotientGroup.mk (diagonal t * A) : SL2 ⧸ Γ)) atTop (cocompact (SL2 ⧸ Γ)) ↔
      ∃ s : ℝ, s ≠ 0 ∧ A⁻¹ * lower s * A ∈ Γ := by
  constructor
  · exact escaping_has_lower Γ hΓ A
  · rintro ⟨s, hs, hmem⟩
    let : DiscreteTopology Γ := hΓ.1
    exact SL2ParabolicRayEscape.divergent Γ A hs hmem

end VeechDichotomy.NativeLatticePointwiseCusp
