module

public import VeechDichotomy.NativeContinuousMeanProfiles

/-! Countably many ACTUAL measurable native phase sets have forward
and backward continuous-time occupation profiles along one common
subsequence for arbitrary tested invariant probabilities. Their mean
integrals are exactly the original set masses. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeIndicatorMeanProfiles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Filter Topology Set
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def observable (B : Set (CompleteOrbits q v)) : CompleteOrbits q v → ℝ := B.indicator (fun _ => 1)

theorem measurable_observable {B : Set (CompleteOrbits q v)} (hB : MeasurableSet B) : Measurable (observable q v B) :=
  measurable_const.indicator hB

theorem observable_bound (B : Set (CompleteOrbits q v)) (x : CompleteOrbits q v) : ‖observable q v B x‖ ≤ 1 := by
  by_cases hx : x ∈ B <;> simp [observable, hx]

def mean (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) (backward : Bool) : KoopmanMeanErgodic.Space μ :=
  NativeContinuousMeanProfiles.mean q v μ hμ (observable q v B) (measurable_observable q v hB) 1 (observable_bound q v B) backward

theorem integral_mean (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) (backward : Bool) :
    ∫ x, mean q v μ hμ B hB backward x ∂μ = (μ B).toReal := by
  calc
    (∫ x, mean q v μ hμ B hB backward x ∂μ) = ∫ x, observable q v B x ∂μ :=
      NativeContinuousMeanProfiles.mean_integral q v μ hμ (observable q v B) (measurable_observable q v hB) 1 (observable_bound q v B) backward
    _ = (μ B).toReal := by simp [observable, integral_indicator hB, Measure.real]

theorem profiles (μ : ℕ → Measure (CompleteOrbits q v)) (hμ : ∀ j, NativeDynamics.InvariantProbability q v (μ j))
    (B : ℕ → Set (CompleteOrbits q v)) (hB : ∀ j, MeasurableSet (B j)) (backward : ℕ → Bool)
    (T : ℕ → ℕ → ℝ) (hT : ∀ j, Tendsto (T j) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, ∀ᵐ x ∂μ j,
      Tendsto (fun k => NativeContinuousMeanProfiles.average q v (observable q v (B j)) (backward j) (T j (σ k)) x) atTop
        (𝓝 (mean q v (μ j) (hμ j) (B j) (hB j) (backward j) x)) :=
  NativeContinuousMeanProfiles.profiles q v μ hμ (fun j => observable q v (B j))
    (fun j => measurable_observable q v (hB j)) (fun _ => 1) (fun _ => zero_le_one)
    (fun j => observable_bound q v (B j)) backward T hT

end VeechDichotomy.NativeIndicatorMeanProfiles
