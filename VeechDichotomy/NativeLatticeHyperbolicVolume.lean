module

public import VeechDichotomy.NativeLatticeLeftVolume
public import VeechDichotomy.SL2HyperbolicVolume

/-! The actual geometric SL2 volume, constructed from hyperbolic area
and compact angular probability, has a genuine positive finite-volume
left-lattice fundamental domain for EVERY native lattice. Haar uniqueness
compares two actual constructed measures, without supplying finite
hyperbolic covolume as an assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeHyperbolicVolume

open LinearGroup NativeVeech NativeLatticeLeftVolume SL2HyperbolicVolume MeasureTheory
open scoped ENNReal

variable (Γ : Subgroup SL2) (hΓ : IsLattice Γ)

theorem geometricVolume_eq_smul : hyperbolicVolume =
    Measure.haarScalarFactor hyperbolicVolume (leftVolume Γ hΓ) • leftVolume Γ hΓ :=
  Measure.isMulLeftInvariant_eq_smul hyperbolicVolume (leftVolume Γ hΓ)

theorem volume_domain : hyperbolicVolume (leftDomain Γ hΓ) =
    (Measure.haarScalarFactor hyperbolicVolume (leftVolume Γ hΓ) : ℝ≥0∞) := by
  calc
    hyperbolicVolume (leftDomain Γ hΓ) =
        (Measure.haarScalarFactor hyperbolicVolume (leftVolume Γ hΓ) • leftVolume Γ hΓ) (leftDomain Γ hΓ) :=
      congrArg (fun ν : Measure SL2 => ν (leftDomain Γ hΓ)) (geometricVolume_eq_smul Γ hΓ)
    _ = _ := by
      rw [Measure.smul_apply]
      change (Measure.haarScalarFactor hyperbolicVolume (leftVolume Γ hΓ) : ℝ≥0∞) *
        leftVolume Γ hΓ (leftDomain Γ hΓ) = _
      rw [volume_leftDomain, mul_one]

theorem volume_domain_pos : 0 < hyperbolicVolume (leftDomain Γ hΓ) := by
  rw [volume_domain]
  exact ENNReal.coe_pos.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _)

theorem volume_domain_lt_top : hyperbolicVolume (leftDomain Γ hΓ) < ∞ := by
  rw [volume_domain]
  exact ENNReal.coe_lt_top

include hΓ in
theorem finite_geometric_fundamentalDomain : ∃ D : Set SL2, MeasurableSet D ∧
    IsFundamentalDomain Γ D hyperbolicVolume ∧ 0 < hyperbolicVolume D ∧ hyperbolicVolume D < ∞ :=
  ⟨leftDomain Γ hΓ, measurable_leftDomain Γ hΓ, isFundamentalDomain Γ hΓ hyperbolicVolume,
    volume_domain_pos Γ hΓ, volume_domain_lt_top Γ hΓ⟩

end VeechDichotomy.NativeLatticeHyperbolicVolume
