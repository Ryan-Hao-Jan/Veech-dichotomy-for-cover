module

public import VeechDichotomy.FlowContinuousProfiles
public import VeechDichotomy.NativeDiscreteMeanProfiles

/-! Actual continuous-time profiles on the complete native directional
flow, in both forward and backward time. Every tested invariant
probability supplies the genuine preserving maps; unit smoothing,
L2 convergence and simultaneous a.e. real-time extraction are proved.
No invariant measure is assumed ergodic or to have positive area weight. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeContinuousMeanProfiles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def signedFlow (backward : Bool) : Flow ℝ (CompleteOrbits q v) :=
  if backward then (flow q v).reverse else flow q v

theorem preserving_signedFlow (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (backward : Bool) (s : ℝ) : MeasurePreserving (signedFlow q v backward s) μ μ := by
  cases backward with
  | false => exact hμ.2 s
  | true => exact hμ.2 (-s)

def average (g : CompleteOrbits q v → ℝ) (backward : Bool) (T : ℝ) (x : CompleteOrbits q v) : ℝ :=
  FlowIntegerAverages.timeAverage (signedFlow q v backward) g T x

def mean (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (g : CompleteOrbits q v → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C)
    (backward : Bool) : KoopmanMeanErgodic.Space μ := by
  let : IsProbabilityMeasure μ := hμ.1
  exact FlowContinuousProfiles.mean (signedFlow q v backward) μ (preserving_signedFlow q v μ hμ backward) g hg C hbound

theorem mean_integral (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (g : CompleteOrbits q v → ℝ) (hg : Measurable g) (C : ℝ) (hbound : ∀ x, ‖g x‖ ≤ C) (backward : Bool) :
    ∫ x, mean q v μ hμ g hg C hbound backward x ∂μ = ∫ x, g x ∂μ := by
  let : IsProbabilityMeasure μ := hμ.1
  exact FlowContinuousProfiles.mean_integral (signedFlow q v backward) μ
    (preserving_signedFlow q v μ hμ backward) g hg C hbound

theorem profiles (μ : ℕ → Measure (CompleteOrbits q v))
    (hμ : ∀ j, NativeDynamics.InvariantProbability q v (μ j))
    (g : ℕ → CompleteOrbits q v → ℝ) (hg : ∀ j, Measurable (g j))
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (hbound : ∀ j x, ‖g j x‖ ≤ C j)
    (backward : ℕ → Bool) (T : ℕ → ℕ → ℝ) (hT : ∀ j, Tendsto (T j) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, ∀ᵐ x ∂μ j,
      Tendsto (fun k => average q v (g j) (backward j) (T j (σ k)) x) atTop
        (𝓝 (mean q v (μ j) (hμ j) (g j) (hg j) (C j) (hbound j) (backward j) x)) := by
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j => (hμ j).1
  exact FlowContinuousProfiles.profiles μ (fun j => signedFlow q v (backward j))
    (fun j => preserving_signedFlow q v (μ j) (hμ j) (backward j)) g hg C hC hbound T hT

end VeechDichotomy.NativeContinuousMeanProfiles
