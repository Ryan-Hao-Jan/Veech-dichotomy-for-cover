module

public import VeechDichotomy.NativeIndicatorMeanProfiles
public import VeechDichotomy.NativeConullSourceSets

/-! Native area and ANY tested invariant probability share ONE
subsequence for countably many actual occupation profiles. The area
profiles also supply a genuine conull set of ORIGINAL source points,
ready for the proved geometric limit-selection argument. The tested
probability need not be ergodic or absolutely continuous. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeTwoMeasureProfiles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Filter Topology Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane) (hv : v ≠ 0)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

private theorem mean_measure_congr (μ ν : Measure (CompleteOrbits q v)) (h : μ = ν)
    (hμ : NativeDynamics.InvariantProbability q v μ) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B) (backward : Bool) (x : CompleteOrbits q v) :
    NativeIndicatorMeanProfiles.mean q v μ hμ B hB backward x =
      NativeIndicatorMeanProfiles.mean q v ν hν B hB backward x := by
  subst ν
  rfl

theorem profiles (ν : Measure (CompleteOrbits q v)) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : ℕ → Set (CompleteOrbits q v)) (hB : ∀ j, MeasurableSet (B j)) (backward : ℕ → Bool)
    (T : ℕ → ℕ → ℝ) (hT : ∀ j, Tendsto (T j) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ᵐ x ∂normalizedCompleteArea q v, ∀ j,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B j)) (backward j) (T j (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B j) (hB j) (backward j) x))) ∧
      (∀ᵐ x ∂ν, ∀ j,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B j)) (backward j) (T j (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v ν hν (B j) (hB j) (backward j) x))) := by
  let μ : ℕ → Measure (CompleteOrbits q v) := fun k => if k % 2 = 0 then normalizedCompleteArea q v else ν
  have hμ : ∀ k, NativeDynamics.InvariantProbability q v (μ k) := by
    intro k
    by_cases hk : k % 2 = 0
    · simpa only [μ, ite_eq_left hk] using NativeDynamics.area_invariantProbability q v hv
    · simpa only [μ, ite_eq_right hk] using hν
  obtain ⟨σ, hσ, hlim⟩ := NativeIndicatorMeanProfiles.profiles q v μ hμ
    (fun k => B (k / 2)) (fun k => hB (k / 2)) (fun k => backward (k / 2)) (fun k => T (k / 2)) (fun k => hT (k / 2))
  refine ⟨σ, hσ, ae_all_iff.mpr (fun j => ?_), ae_all_iff.mpr (fun j => ?_)⟩
  · have hrow := hlim (2 * j)
    have hidx : (2 * j) / 2 = j := by omega
    simp only [hidx] at hrow
    have hm : ∀ x, NativeIndicatorMeanProfiles.mean q v (μ (2 * j)) (hμ (2 * j)) (B j) (hB j) (backward j) x =
        NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B j) (hB j) (backward j) x :=
      fun x => mean_measure_congr q v _ _ (by simp [μ]) _ _ _ _ _ x
    simp_rw [hm] at hrow
    simpa [μ] using hrow
  · have hrow := hlim (2 * j + 1)
    have hidx : (2 * j + 1) / 2 = j := by omega
    simp only [hidx] at hrow
    have hm : ∀ x, NativeIndicatorMeanProfiles.mean q v (μ (2 * j + 1)) (hμ (2 * j + 1)) (B j) (hB j) (backward j) x =
        NativeIndicatorMeanProfiles.mean q v ν hν (B j) (hB j) (backward j) x :=
      fun x => mean_measure_congr q v _ _ (by simp [μ]) _ _ _ _ _ x
    simp_rw [hm] at hrow
    simpa [μ] using hrow

theorem source_and_test (ν : Measure (CompleteOrbits q v)) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : ℕ → Set (CompleteOrbits q v)) (hB : ∀ j, MeasurableSet (B j)) (backward : ℕ → Bool)
    (T : ℕ → ℕ → ℝ) (hT : ∀ j, Tendsto (T j) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ E : Set X, MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0 ∧
      (∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ ∀ j,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B j)) (backward j) (T j (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B j) (hB j) (backward j) x))) ∧
      (∀ᵐ x ∂ν, ∀ j,
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B j)) (backward j) (T j (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v ν hν (B j) (hB j) (backward j) x))) := by
  obtain ⟨σ, hσ, harea, htest⟩ := profiles q v hv ν hν B hB backward T hT
  obtain ⟨E, hE, hEP⟩ := NativeConullSourceSets.conull_source_set q v hv _ harea
  exact ⟨σ, hσ, E, hE, hEP, htest⟩

end VeechDichotomy.NativeTwoMeasureProfiles
