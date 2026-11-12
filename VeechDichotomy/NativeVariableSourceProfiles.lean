module

public import VeechDichotomy.NativeVaryingOccupation

/-! GENUINE conull source sets and tested-probability a.e. sets carrying
all varying positive-ratio and shifted-interval occupation profiles.
The uncountable family of endpoint sequences is controlled pointwise
by the proved countable rational tests, without an uncountable AE intersection. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeVariableSourceProfiles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Set Filter Topology
open VaryingOccupationProfiles
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def StableProfile (B : Set (CompleteOrbits q v)) (R : ℕ → ℝ) (x : CompleteOrbits q v) (m : ℝ) : Prop :=
  (∀ (backward : Bool) (T : ℕ → ℝ) (a : ℝ), Tendsto (fun k => T k / R k) atTop (𝓝 a) → 0 < a →
    Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v B) backward (T k) x) atTop (𝓝 m)) ∧
  (∀ (A B' : ℕ → ℝ) (a b : ℝ), Tendsto (fun k => A k / R k) atTop (𝓝 a) →
    Tendsto (fun k => B' k / R k) atTop (𝓝 b) → a < b →
      Tendsto (fun k => (B' k - A k)⁻¹ * ∫ s in A k..B' k, NativeIndicatorMeanProfiles.observable q v B (flow q v s x)) atTop (𝓝 m))

theorem of_rational (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (x : CompleteOrbits q v) (m : ℝ)
    (hprof : ∀ (a : PositiveRational) (backward : Bool),
      Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v B) backward ((a.val : ℝ) * R k) x) atTop (𝓝 m)) :
    StableProfile q v B R x m :=
  ⟨fun backward _ _ ha hp => NativeVaryingOccupation.varying_average q v B hB R hR x m hprof backward ha hp,
    fun _ _ _ _ hA hB' hab => NativeVaryingOccupation.interval_average q v B hB R hR x m hprof hA hB' hab⟩

theorem source_and_test (hv : v ≠ 0) (ν : Measure (CompleteOrbits q v)) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : ℕ → Set (CompleteOrbits q v)) (hB : ∀ j, MeasurableSet (B j)) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ E : Set X, MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0 ∧
      (∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ ∀ j,
        StableProfile q v (B j) (R ∘ σ) x
          (NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B j) (hB j) false x)) ∧
      (∀ᵐ x ∂ν, ∀ j, StableProfile q v (B j) (R ∘ σ) x (NativeIndicatorMeanProfiles.mean q v ν hν (B j) (hB j) false x)) := by
  obtain ⟨σ, hσ, E, hE, harea, htest⟩ := NativeRationalProfiles.source_and_test q v hv ν hν B hB R hR
  have hRσ : Tendsto (R ∘ σ) atTop atTop := hR.comp hσ.tendsto_atTop
  refine ⟨σ, hσ, E, hE, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hxz, hprof⟩ := harea z hz
    exact ⟨x, hxz, fun j => of_rational q v (B j) (hB j) (R ∘ σ) hRσ x _ (hprof j)⟩
  · filter_upwards [htest] with x hx
    exact fun j => of_rational q v (B j) (hB j) (R ∘ σ) hRσ x _ (hx j)

end VeechDichotomy.NativeVariableSourceProfiles
