module

public import MNEC.NativeDifferentialEquivFlatness
public import VeechDichotomy.NativeDynamics
public import VeechDichotomy.InvariantProbabilityTransport

/-! A genuine native differential equivalence preserves actual complete
directional flows, minimality and unique ergodicity. The regular flatness
and ODE conjugacy are proved in the native foundation, not assumed as
additional equivalence fields. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDifferentialEquivalenceDynamics

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeDifferentialEquiv
open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {q : Differential X} {r : Differential Y} (e : Equiv q r)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩
local instance : MeasurableSpace Y := borel Y
local instance : BorelSpace Y := ⟨rfl⟩

theorem complete_iff (v : Plane) (x : Regular q) :
    regularHomeomorph e x ∈ completeOrbitSet r v ↔ x ∈ completeOrbitSet q v := by
  change MNEC.NativeDirectionalDynamics.domain r v (regularHomeomorph e x) = univ ↔
    MNEC.NativeDirectionalDynamics.domain q v x = univ
  rw [MNEC.NativeDifferentialEquivFlatness.domain_eq e v x]

def completeHomeomorph (v : Plane) : CompleteOrbits q v ≃ₜ CompleteOrbits r v where
  toFun x := ⟨regularHomeomorph e x.val, (complete_iff e v x.val).mpr x.property⟩
  invFun y := ⟨(regularHomeomorph e).symm y.val, (complete_iff e v _).mp (by
    simpa only [Homeomorph.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext ((regularHomeomorph e).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((regularHomeomorph e).apply_symm_apply y.val)
  continuous_toFun := ((regularHomeomorph e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((regularHomeomorph e).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem flow_conjugacy (v : Plane) (t : ℝ) (x : CompleteOrbits q v) :
    completeHomeomorph e v (flow q v t x) = flow r v t (completeHomeomorph e v x) := by
  apply Subtype.ext
  exact MNEC.NativeDifferentialEquivFlatness.trajectory_conjugacy e v x.val t (complete_time_mem q v x t)

theorem surface_orbit_relation (v : Plane) (t : ℝ) (x : CompleteOrbits q v) :
    (flow r v t (completeHomeomorph e v x)).val.val = e.homeomorph (flow q v t x).val.val :=
  (congrArg (fun y : CompleteOrbits r v => y.val.val) (flow_conjugacy e v t x)).symm

theorem orbit_dense_iff (v : Plane) (x : CompleteOrbits q v) :
    DenseRange (fun t : ℝ => (flow q v t x).val.val) ↔
      DenseRange (fun t : ℝ => (flow r v t (completeHomeomorph e v x)).val.val) := by
  constructor
  · intro h
    have hd := e.homeomorph.surjective.denseRange.comp h e.homeomorph.continuous
    convert hd using 1
    funext t
    exact surface_orbit_relation e v t x
  · intro h
    have hd := e.homeomorph.symm.surjective.denseRange.comp h e.homeomorph.symm.continuous
    simpa only [Function.comp_def, surface_orbit_relation, Homeomorph.symm_apply_apply] using hd

include e in
theorem minimalDirection_iff (v : Plane) : NativeDynamics.MinimalDirection q v ↔ NativeDynamics.MinimalDirection r v := by
  constructor
  · intro h
    refine ⟨h.1, fun y => ?_⟩
    have hd := (orbit_dense_iff e v ((completeHomeomorph e v).symm y)).mp (h.2 ((completeHomeomorph e v).symm y))
    simpa only [Homeomorph.apply_symm_apply] using hd
  · intro h
    exact ⟨h.1, fun x => (orbit_dense_iff e v x).mpr (h.2 (completeHomeomorph e v x))⟩

include e in
theorem unique_invariant_probability_iff (v : Plane) :
    (∃! μ : Measure (CompleteOrbits q v), NativeDynamics.InvariantProbability q v μ) ↔
      ∃! ν : Measure (CompleteOrbits r v), NativeDynamics.InvariantProbability r v ν := by
  let H := (completeHomeomorph e v).toMeasurableEquiv
  have hc : ∀ (t : ℝ) (x : CompleteOrbits q v), H (timeMap q v t x) = timeMap r v t (H x) :=
    fun t x => flow_conjugacy e v t x
  have h := InvariantProbabilityTransport.existsUnique_iff H (timeMap q v) (timeMap r v) hc
    (measurable_timeMap q v) (measurable_timeMap r v)
  simpa only [InvariantProbabilityTransport.InvariantFor, NativeDynamics.InvariantProbability] using h

include e in
theorem uniquelyErgodicDirection_iff (v : Plane) :
    NativeDynamics.UniquelyErgodicDirection q v ↔ NativeDynamics.UniquelyErgodicDirection r v := by
  by_cases hv : v = 0
  · simp only [NativeDynamics.UniquelyErgodicDirection, hv, ne_eq, not_true_eq_false, false_and]
  · rw [NativeDynamics.uniquelyErgodic_iff_unique_invariantProbability q v hv,
      NativeDynamics.uniquelyErgodic_iff_unique_invariantProbability r v hv]
    exact unique_invariant_probability_iff e v

end VeechDichotomy.NativeDifferentialEquivalenceDynamics
