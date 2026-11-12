module

public import VeechDichotomy.CountableKoopmanProfiles
public import VeechDichotomy.NativeDynamics

/-! Statistical profiles for the ACTUAL complete native flow and its
actual invariant probabilities. Countably many observables, positive
or negative sampling steps, measures and diverging integer lengths
share one a.e. convergent subsequence. No ergodicity hypothesis is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDiscreteMeanProfiles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Filter Topology Finset
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem iterate_timeMap (a : ℝ) (n : ℕ) (x : CompleteOrbits q v) :
    (timeMap q v a)^[n] x = timeMap q v ((n : ℝ) * a) x := by
  induction n generalizing x with
  | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, timeMap_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, ← timeMap_add]
    congr 1
    simp only [Nat.cast_succ]
    ring

def sampleAverage (g : CompleteOrbits q v → ℝ) (a : ℝ) (n : ℕ) (x : CompleteOrbits q v) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ range n, g (timeMap q v ((k : ℝ) * a) x)

theorem sampleAverage_eq_birkhoff (g : CompleteOrbits q v → ℝ) (a : ℝ) (n : ℕ) (x : CompleteOrbits q v) :
    sampleAverage q v g a n x = birkhoffAverage ℝ (timeMap q v a) g n x := by
  simp only [sampleAverage, birkhoffAverage, birkhoffSum, smul_eq_mul, iterate_timeMap]

theorem profiles (μ : ℕ → Measure (CompleteOrbits q v))
    (hμ : ∀ j, NativeDynamics.InvariantProbability q v (μ j))
    (g : ∀ j, KoopmanMeanErgodic.Space (μ j)) (a : ℕ → ℝ)
    (n : ℕ → ℕ → ℕ) (hn : ∀ j, Tendsto (n j) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, ∀ᵐ x ∂μ j,
      Tendsto (fun k => sampleAverage q v (g j) (a j) (n j (σ k)) x) atTop
        (𝓝 (KoopmanMeanErgodic.limit (μ j) (timeMap q v (a j)) ((hμ j).2 (a j)) (g j) x)) := by
  obtain ⟨σ, hσ, hlim⟩ := CountableKoopmanProfiles.simultaneous μ (fun j => timeMap q v (a j))
    (fun j => (hμ j).2 (a j)) g n hn
  refine ⟨σ, hσ, ?_⟩
  intro j
  filter_upwards [hlim j] with x hx
  simpa only [sampleAverage_eq_birkhoff] using hx

end VeechDichotomy.NativeDiscreteMeanProfiles
