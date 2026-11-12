module

public import VeechDichotomy.FlowReverseMeans
public import VeechDichotomy.NativeIndicatorMeanProfiles

/-! Both time directions of the ACTUAL native flow have identical
occupation mean vectors and representatives. This identifies the means;
the actual statistical convergence statements remain a.e. statements. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeReverseMeans

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem continuous_mean_reverse (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (g : CompleteOrbits q v → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) :
    NativeContinuousMeanProfiles.mean q v μ hμ g hg C hbound true =
      NativeContinuousMeanProfiles.mean q v μ hμ g hg C hbound false := by
  let : IsProbabilityMeasure μ := hμ.1
  exact FlowReverseMeans.mean_reverse (flow q v) g μ (fun s => hμ.2 s) hg C hbound

theorem indicator_mean_reverse (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) :
    NativeIndicatorMeanProfiles.mean q v μ hμ B hB true = NativeIndicatorMeanProfiles.mean q v μ hμ B hB false :=
  continuous_mean_reverse q v μ hμ (NativeIndicatorMeanProfiles.observable q v B)
    (NativeIndicatorMeanProfiles.measurable_observable q v hB) 1 (NativeIndicatorMeanProfiles.observable_bound q v B)

theorem indicator_mean_direction (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) (backward : Bool) :
    NativeIndicatorMeanProfiles.mean q v μ hμ B hB backward = NativeIndicatorMeanProfiles.mean q v μ hμ B hB false := by
  cases backward with
  | false => rfl
  | true => exact indicator_mean_reverse q v μ hμ B hB

theorem indicator_mean_apply (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) (backward : Bool) (x : CompleteOrbits q v) :
    NativeIndicatorMeanProfiles.mean q v μ hμ B hB backward x = NativeIndicatorMeanProfiles.mean q v μ hμ B hB false x :=
  congrArg (fun h : KoopmanMeanErgodic.Space μ => h x) (indicator_mean_direction q v μ hμ B hB backward)

theorem backward_average (g : CompleteOrbits q v → ℝ) (T : ℝ) (x : CompleteOrbits q v) :
    NativeContinuousMeanProfiles.average q v g true T x = T⁻¹ * ∫ s in -T..0, g (flow q v s x) := by
  change T⁻¹ * (∫ s in (0 : ℝ)..T, g ((flow q v).reverse s x)) = _
  congr 1
  simpa only [Flow.reverse_apply, zero_sub, sub_zero, neg_zero] using
    intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := T) (fun s => g (flow q v s x)) (0 : ℝ)

end VeechDichotomy.NativeReverseMeans
