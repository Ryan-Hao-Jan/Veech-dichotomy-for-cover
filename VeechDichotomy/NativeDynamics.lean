module

public import MNEC.NativeConullDirectionalOrbits
public import MNEC.NativeProbabilityArea
public import MNEC.NativeCompleteDirectionalArea

/-!
Directional dynamics on the ACTUAL complete nonsingular trajectories of
a native holomorphic differential. The flow, area, AE completeness and
finite positive area are all constructed in the imported proofs.

No recurrence or unique-ergodicity theorem is assumed here.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDynamics

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea
open MeasureTheory Set Topology
open scoped Manifold ContDiff ENNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- Every complete nonsingular trajectory is dense in the original surface. -/
def MinimalDirection (q : Differential X) (v : Plane) : Prop :=
  v ≠ 0 ∧ ∀ x : CompleteOrbits q v,
    DenseRange (fun t : ℝ => (flow q v t x).val.val)

/-- A probability measure invariant under every actual time map. -/
def InvariantProbability (q : Differential X) (v : Plane)
    (μ : Measure (CompleteOrbits q v)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t : ℝ, MeasurePreserving (timeMap q v t) μ μ

/-- Flat area is the unique invariant probability on the nonsingular flow. -/
def UniquelyErgodicDirection (q : Differential X) (v : Plane) : Prop :=
  v ≠ 0 ∧ ∀ μ : Measure (CompleteOrbits q v),
    InvariantProbability q v μ → μ = normalizedCompleteArea q v

theorem completeArea_full_mass (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    completeArea q v univ = MNEC.NativeRegularArea.regularArea q univ := by
  rw [completeArea_univ,
    measure_congr (MNEC.NativeConullDirectionalOrbits.completeSet_ae_eq_univ q v hv)]

theorem normalizedCompleteArea_probability (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    IsProbabilityMeasure (normalizedCompleteArea q v) where
  measure_univ := by
    rw [normalizedCompleteArea, Measure.smul_apply, smul_eq_mul, completeArea_full_mass q v hv]
    exact ENNReal.inv_mul_cancel (MNEC.NativeFiniteRegularArea.regularArea_univ_pos q).ne'
      (MNEC.NativeFiniteRegularArea.regularArea_univ_ne_top q)

theorem area_invariantProbability (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    InvariantProbability q v (normalizedCompleteArea q v) :=
  ⟨normalizedCompleteArea_probability q v hv, normalized_timeMap_measurePreserving q v⟩

theorem completeOrbits_nonempty (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    Nonempty (CompleteOrbits q v) := by
  let : IsProbabilityMeasure (normalizedCompleteArea q v) :=
    normalizedCompleteArea_probability q v hv
  exact nonempty_of_isProbabilityMeasure (normalizedCompleteArea q v)

theorem uniquelyErgodic_iff_unique_invariantProbability
    (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    UniquelyErgodicDirection q v ↔
      ∃! μ : Measure (CompleteOrbits q v), InvariantProbability q v μ := by
  constructor
  · intro h
    exact ⟨normalizedCompleteArea q v, area_invariantProbability q v hv, h.2⟩
  · rintro ⟨μ, hμ, huniq⟩
    refine ⟨hv, fun ν hν => ?_⟩
    exact (huniq ν hν).trans (huniq _ (area_invariantProbability q v hv)).symm

end VeechDichotomy.NativeDynamics
