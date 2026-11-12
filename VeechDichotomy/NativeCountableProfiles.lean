module

public import VeechDichotomy.NativeReverseMeans
public import VeechDichotomy.NativeTwoMeasureProfiles
public import Mathlib.Basic.Countable.Defs

/-! Arbitrary countable families of native occupation tests share one
area/tested-probability subsequence. All forward/backward profiles have
the SAME proved forward mean. Countable enumeration is constructed,
and original-source conull sets carry the actual profiles. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeCountableProfiles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Filter Topology Set
open scoped Manifold ContDiff

variable {X ι : Type*} [Countable ι] [Nonempty ι]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane) (hv : v ≠ 0)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem profiles (ν : Measure (CompleteOrbits q v)) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : ι → Set (CompleteOrbits q v)) (hB : ∀ i, MeasurableSet (B i)) (backward : ι → Bool)
    (T : ι → ℕ → ℝ) (hT : ∀ i, Tendsto (T i) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ᵐ x ∂normalizedCompleteArea q v, ∀ i,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B i)) (backward i) (T i (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B i) (hB i) false x))) ∧
      (∀ᵐ x ∂ν, ∀ i,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B i)) (backward i) (T i (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v ν hν (B i) (hB i) false x))) := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  obtain ⟨σ, hσ, harea, htest⟩ := NativeTwoMeasureProfiles.profiles q v hv ν hν
    (B ∘ e) (fun n => hB (e n)) (backward ∘ e) (T ∘ e) (fun n => hT (e n))
  refine ⟨σ, hσ, ?_, ?_⟩
  · filter_upwards [harea] with x hx
    intro i
    obtain ⟨n, rfl⟩ := he i
    simpa only [Function.comp_apply, NativeReverseMeans.indicator_mean_apply] using hx n
  · filter_upwards [htest] with x hx
    intro i
    obtain ⟨n, rfl⟩ := he i
    simpa only [Function.comp_apply, NativeReverseMeans.indicator_mean_apply] using hx n

theorem source_and_test (ν : Measure (CompleteOrbits q v)) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : ι → Set (CompleteOrbits q v)) (hB : ∀ i, MeasurableSet (B i)) (backward : ι → Bool)
    (T : ι → ℕ → ℝ) (hT : ∀ i, Tendsto (T i) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ E : Set X, MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0 ∧
      (∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ ∀ i,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B i)) (backward i) (T i (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B i) (hB i) false x))) ∧
      (∀ᵐ x ∂ν, ∀ i,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B i)) (backward i) (T i (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v ν hν (B i) (hB i) false x))) := by
  obtain ⟨σ, hσ, harea, htest⟩ := profiles q v hv ν hν B hB backward T hT
  obtain ⟨E, hE, hEP⟩ := NativeConullSourceSets.conull_source_set q v hv _ harea
  exact ⟨σ, hσ, E, hE, hEP, htest⟩

end VeechDichotomy.NativeCountableProfiles
