module

public import VeechDichotomy.NativeLatticeQuotient
public import VeechDichotomy.SL2Borel
public import VeechDichotomy.DiscreteQuotientLiftHaar
public import VeechDichotomy.DiscreteQuotientFundamentalDomain

/-! The native lattice hypothesis supplies an actual normalized Haar
volume on SL2 and an actual measurable right-lattice fundamental domain
of volume one. This derives finite covolume from the stated invariant
quotient probability without a normal-subgroup assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeHaarVolume

open LinearGroup NativeVeech NativeLatticeQuotient MeasureTheory
open scoped ENNReal

variable (Γ : Subgroup SL2) (hΓ : IsLattice Γ)

def haarVolume : Measure SL2 := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  exact DiscreteQuotientMeasureLift.lift Γ (invariantMeasure Γ hΓ)

instance haarVolume_haar : Measure.IsHaarMeasure (haarVolume Γ hΓ) := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  change Measure.IsHaarMeasure (DiscreteQuotientMeasureLift.lift Γ (invariantMeasure Γ hΓ))
  infer_instance

def fundamentalDomain : Set SL2 := by
  let : DiscreteTopology Γ := hΓ.1
  exact DiscreteQuotientFundamentalDomain.domain Γ

theorem measurable_fundamentalDomain : MeasurableSet (fundamentalDomain Γ hΓ) := by
  let : DiscreteTopology Γ := hΓ.1
  exact DiscreteQuotientFundamentalDomain.measurable_domain Γ

theorem isFundamentalDomain : IsFundamentalDomain Γ.op (fundamentalDomain Γ hΓ) (haarVolume Γ hΓ) := by
  let : DiscreteTopology Γ := hΓ.1
  exact DiscreteQuotientFundamentalDomain.isFundamentalDomain Γ (haarVolume Γ hΓ)

theorem volume_fundamentalDomain : haarVolume Γ hΓ (fundamentalDomain Γ hΓ) = 1 := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  exact (DiscreteQuotientFundamentalDomain.measure_domain Γ (invariantMeasure Γ hΓ)).trans measure_univ

end VeechDichotomy.NativeLatticeHaarVolume
