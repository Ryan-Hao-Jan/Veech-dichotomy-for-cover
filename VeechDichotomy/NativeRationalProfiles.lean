module

public import VeechDichotomy.NativeCountableProfiles
public import VeechDichotomy.VaryingOccupationProfiles

/-! Actual native source/test profiles simultaneously at EVERY
positive rational multiple of a diverging reference time, in BOTH
directions, with the SAME actual mean for each measurable set. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRationalProfiles

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Filter Topology Set
open VaryingOccupationProfiles
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane) (hv : v ≠ 0)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem source_and_test (ν : Measure (CompleteOrbits q v)) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : ℕ → Set (CompleteOrbits q v)) (hB : ∀ j, MeasurableSet (B j)) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ E : Set X, MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0 ∧
      (∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ ∀ j (a : PositiveRational) (backward : Bool),
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B j)) backward ((a.val : ℝ) * R (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B j) (hB j) false x))) ∧
      (∀ᵐ x ∂ν, ∀ j (a : PositiveRational) (backward : Bool),
        Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v (B j)) backward ((a.val : ℝ) * R (σ k)) x) atTop
          (𝓝 (NativeIndicatorMeanProfiles.mean q v ν hν (B j) (hB j) false x))) := by
  let : Nonempty PositiveRational := ⟨⟨1, by decide⟩⟩
  let ι := PositiveRational × Bool × ℕ
  let sets : ι → Set (CompleteOrbits q v) := fun i => B i.2.2
  let dir : ι → Bool := fun i => i.2.1
  let times : ι → ℕ → ℝ := fun i n => (i.1.val : ℝ) * R n
  have htimes : ∀ i : ι, Tendsto (times i) atTop atTop := by
    intro i
    exact Filter.Tendsto.const_mul_atTop (by exact_mod_cast i.1.property) hR
  obtain ⟨σ, hσ, E, hE, hEP, htest⟩ := NativeCountableProfiles.source_and_test q v hv ν hν
    sets (fun i => hB i.2.2) dir times htimes
  refine ⟨σ, hσ, E, hE, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hxz, hprof⟩ := hEP z hz
    exact ⟨x, hxz, fun j a backward => hprof (a, backward, j)⟩
  · filter_upwards [htest] with x hx
    exact fun j a backward => hx (a, backward, j)

end VeechDichotomy.NativeRationalProfiles
