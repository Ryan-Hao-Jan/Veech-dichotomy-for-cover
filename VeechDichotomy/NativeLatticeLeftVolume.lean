module

public import VeechDichotomy.NativeLatticeHaarVolume
public import VeechDichotomy.SL2Unimodular
public import VeechDichotomy.DiscreteLeftFundamentalDomain

/-! An actual normalized left-lattice fundamental domain and Haar
volume from the native right-coset invariant probability. Inversion
transports the constructed representatives and their volume; the proved
SL2 unimodularity supplies left invariance of the inverted measure. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeLeftVolume

open LinearGroup NativeVeech NativeLatticeQuotient NativeLatticeHaarVolume MeasureTheory

variable (Γ : Subgroup SL2) (hΓ : IsLattice Γ)

def leftVolume : Measure SL2 := (haarVolume Γ hΓ).inv

instance leftVolume_haar : Measure.IsHaarMeasure (leftVolume Γ hΓ) := by
  change Measure.IsHaarMeasure (haarVolume Γ hΓ).inv
  exact { toIsFiniteMeasureOnCompacts := inferInstance
          toIsMulLeftInvariant := inferInstance
          toIsOpenPosMeasure := inferInstance }

def leftDomain : Set SL2 := by
  let : DiscreteTopology Γ := hΓ.1
  exact DiscreteLeftFundamentalDomain.leftDomain Γ

theorem measurable_leftDomain : MeasurableSet (leftDomain Γ hΓ) := by
  let : DiscreteTopology Γ := hΓ.1
  exact DiscreteLeftFundamentalDomain.measurable_leftDomain Γ

theorem isFundamentalDomain (ν : Measure SL2) : IsFundamentalDomain Γ (leftDomain Γ hΓ) ν := by
  let : DiscreteTopology Γ := hΓ.1
  exact DiscreteLeftFundamentalDomain.isFundamentalDomain Γ ν

theorem volume_leftDomain : leftVolume Γ hΓ (leftDomain Γ hΓ) = 1 := by
  let : DiscreteTopology Γ := hΓ.1
  let : Countable Γ := countable_of_Lindelof_of_discrete
  exact (DiscreteLeftFundamentalDomain.inv_lift_mass Γ (invariantMeasure Γ hΓ)).trans measure_univ

end VeechDichotomy.NativeLatticeLeftVolume
