module

public import VeechDichotomy.NativeDynamics
public import VeechDichotomy.InvariantProbabilityTransport
public import MNEC.NativeVelocityTimeScaling

/-! Nonzero scalar changes of actual native velocities only rescale the
clock. The complete-phase identification, orbit sets, minimality and
unique ergodicity are proved without importing the old genus-two spectrum
interfaces. This supports testing the contracted direction as vertical.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativeDirectionRescaling

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeVelocityTimeScaling
open MeasureTheory Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def phaseHomeomorph (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane) :
    CompleteOrbits q (a • v) ≃ₜ CompleteOrbits q v :=
  Homeomorph.setCongr (completeOrbitSet_smul q a ha v)

theorem flow_clock (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane)
    (t : ℝ) (x : CompleteOrbits q (a • v)) :
    phaseHomeomorph q a ha v (flow q (a • v) t x) =
      flow q v (t * a) (phaseHomeomorph q a ha v x) := by
  apply Subtype.ext
  exact MNEC.NativeVelocityTimeScaling.trajectory_smul q a ha v x.val t
    (complete_time_mem q (a • v) x t)

theorem orbit_range (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane)
    (x : CompleteOrbits q (a • v)) :
    range (fun t : ℝ => (flow q (a • v) t x).val.val) =
      range (fun t : ℝ => (flow q v t (phaseHomeomorph q a ha v x)).val.val) := by
  have hpoint (t : ℝ) : (flow q (a • v) t x).val.val =
      (flow q v (t * a) (phaseHomeomorph q a ha v x)).val.val :=
    congrArg (fun y : CompleteOrbits q v => y.val.val) (flow_clock q a ha v t x)
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t * a, (hpoint t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t / a, ?_⟩
    dsimp only
    rw [hpoint, div_mul_cancel₀ _ ha]

theorem minimalDirection_iff (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane) :
    NativeDynamics.MinimalDirection q (a • v) ↔ NativeDynamics.MinimalDirection q v := by
  have hne : a • v ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro h hv
      apply h
      rw [hv, smul_zero]
    · intro h hv
      exact h ((smul_eq_zero.mp hv).resolve_left ha)
  have hd (x : CompleteOrbits q (a • v)) :
      DenseRange (fun t : ℝ => (flow q (a • v) t x).val.val) ↔
        DenseRange (fun t : ℝ => (flow q v t (phaseHomeomorph q a ha v x)).val.val) := by
    change Dense (range _) ↔ Dense (range _)
    rw [orbit_range]
  constructor
  · intro h
    refine ⟨hne.mp h.1, fun y => ?_⟩
    have hdy := (hd ((phaseHomeomorph q a ha v).symm y)).mp
      (h.2 ((phaseHomeomorph q a ha v).symm y))
    simpa only [Homeomorph.apply_symm_apply] using hdy
  · intro h
    exact ⟨hne.mpr h.1, fun x => (hd x).mpr (h.2 (phaseHomeomorph q a ha v x))⟩

theorem unique_invariant_probability_iff (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane) :
    (∃! μ : Measure (CompleteOrbits q (a • v)), NativeDynamics.InvariantProbability q (a • v) μ) ↔
      ∃! ν : Measure (CompleteOrbits q v), NativeDynamics.InvariantProbability q v ν := by
  let e := (phaseHomeomorph q a ha v).toMeasurableEquiv
  have hconj : ∀ (t : ℝ) (x : CompleteOrbits q (a • v)),
      e (timeMap q (a • v) t x) = timeMap q v (t * a) (e x) := by
    intro t x
    exact flow_clock q a ha v t x
  have h := InvariantProbabilityTransport.existsUnique_iff e (timeMap q (a • v))
    (fun t => timeMap q v (t * a)) hconj (measurable_timeMap q (a • v))
    (fun t => measurable_timeMap q v (t * a))
  have hclock : Function.Surjective (fun t : ℝ => t * a) :=
    fun t => ⟨t / a, div_mul_cancel₀ t ha⟩
  have hc := InvariantProbabilityTransport.existsUnique_clock_iff (timeMap q v) (fun t => t * a) hclock
  simpa only [InvariantProbabilityTransport.InvariantFor, NativeDynamics.InvariantProbability] using h.trans hc

theorem uniquelyErgodicDirection_iff (q : Differential X) (a : ℝ) (ha : a ≠ 0) (v : Plane) :
    NativeDynamics.UniquelyErgodicDirection q (a • v) ↔ NativeDynamics.UniquelyErgodicDirection q v := by
  by_cases hv : v = 0
  · simp only [NativeDynamics.UniquelyErgodicDirection, hv, smul_zero, ne_eq, not_true_eq_false, false_and]
  · have hav : a • v ≠ 0 := smul_ne_zero ha hv
    rw [NativeDynamics.uniquelyErgodic_iff_unique_invariantProbability q (a • v) hav,
      NativeDynamics.uniquelyErgodic_iff_unique_invariantProbability q v hv]
    exact unique_invariant_probability_iff q a ha v

end VeechDichotomy.NativeDirectionRescaling
