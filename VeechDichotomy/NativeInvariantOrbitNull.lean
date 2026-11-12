module

public import VeechDichotomy.FreeFlowOrbitNull
public import VeechDichotomy.NativeMinimalOrbitVisits

/-! Every individual actual complete minimal orbit is null for EVERY
tested invariant probability. Consequently countably many arbitrary
original-surface endpoints are avoided at ALL times almost everywhere,
including endpoints that do not belong to any complete orbit. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeInvariantOrbitNull

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem orbit_null (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (hmin : NativeDynamics.MinimalDirection q v) (x : CompleteOrbits q v) :
    μ (range (fun t : ℝ => flow q v t x)) = 0 := by
  let : IsProbabilityMeasure μ := hμ.1
  apply FreeFlowOrbitNull.orbit_null (flow q v) μ (fun t => hμ.2 t) x
  intro s t hst
  apply NativeMinimalOrbitVisits.trajectory_injective q v hmin x
  exact congrArg Subtype.val hst

theorem endpoint_avoid (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (hmin : NativeDynamics.MinimalDirection q v) (z : X) :
    ∀ᵐ y ∂μ, ∀ t : ℝ, (flow q v t y).val.val ≠ z := by
  by_cases hz : ∃ x : CompleteOrbits q v, x.val.val = z
  · obtain ⟨x, hxz⟩ := hz
    have hnull : μ (FreeFlowOrbitNull.reaching (flow q v) x) = 0 := by
      rw [FreeFlowOrbitNull.reaching_eq_range]
      exact orbit_null q v μ hμ hmin x
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
    intro t ht
    apply hy
    exact ⟨t, Subtype.ext (Subtype.ext (ht.trans hxz.symm))⟩
  · exact Eventually.of_forall (fun y t ht => hz ⟨flow q v t y, ht⟩)

theorem countable_endpoints (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (hmin : NativeDynamics.MinimalDirection q v) (z : ℕ → X) :
    ∀ᵐ y ∂μ, ∀ j : ℕ, ∀ t : ℝ, (flow q v t y).val.val ≠ z j :=
  ae_all_iff.mpr (fun j => endpoint_avoid q v μ hμ hmin (z j))

end VeechDichotomy.NativeInvariantOrbitNull
