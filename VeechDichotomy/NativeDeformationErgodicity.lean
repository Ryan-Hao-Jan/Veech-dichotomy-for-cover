module

public import VeechDichotomy.NativeDeformationFlow
public import VeechDichotomy.InvariantProbabilityTransport

/-! Unique ergodicity is preserved by the ACTUAL native deformation and
its constructed complete-flow conjugacy. Invariant probabilities are
transported by the derived Borel phase-space homeomorphism; the actual
canonical area is already proved to be an invariant probability on both
curves. No area-preservation theorem is assumed as an input here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace VeechDichotomy.NativeDeformationErgodicity

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeCompleteDirectionalFlow
open NativeDeformationRegular NativeDeformationFlow LinearGroup LinearEquivalences WholeDeformedAtlas
open MeasureTheory Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (A : SL2)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩
local instance : MeasurableSpace (WholeSurface q A) := borel (WholeSurface q A)
local instance : BorelSpace (WholeSurface q A) := ⟨rfl⟩

theorem unique_invariant_probability_iff (v : Plane) :
    (∃! μ : Measure (CompleteOrbits q v), NativeDynamics.InvariantProbability q v μ) ↔
      ∃! ν : Measure (CompleteOrbits (transformed q A) (planeEquiv A v)),
        NativeDynamics.InvariantProbability (transformed q A) (planeEquiv A v) ν := by
  let e := (completeHomeomorph q A v).toMeasurableEquiv
  have hconj : ∀ (t : ℝ) (x : CompleteOrbits q v),
      e (timeMap q v t x) = timeMap (transformed q A) (planeEquiv A v) t (e x) := by
    intro t x
    exact flow_conjugacy q A v t x
  have h := InvariantProbabilityTransport.existsUnique_iff e
    (timeMap q v) (timeMap (transformed q A) (planeEquiv A v)) hconj
    (measurable_timeMap q v) (measurable_timeMap (transformed q A) (planeEquiv A v))
  simpa only [InvariantProbabilityTransport.InvariantFor, NativeDynamics.InvariantProbability] using h

theorem uniquelyErgodicDirection_iff (v : Plane) :
    NativeDynamics.UniquelyErgodicDirection q v ↔
      NativeDynamics.UniquelyErgodicDirection (transformed q A) (planeEquiv A v) := by
  by_cases hv : v = 0
  · simp only [NativeDynamics.UniquelyErgodicDirection, hv, map_zero, ne_eq, not_true_eq_false, false_and]
  · have hAv : planeEquiv A v ≠ 0 := by
      intro h
      exact hv ((planeEquiv A).injective (h.trans (map_zero (planeEquiv A)).symm))
    rw [NativeDynamics.uniquelyErgodic_iff_unique_invariantProbability q v hv,
      NativeDynamics.uniquelyErgodic_iff_unique_invariantProbability (transformed q A) (planeEquiv A v) hAv]
    exact unique_invariant_probability_iff q A v

end VeechDichotomy.NativeDeformationErgodicity
