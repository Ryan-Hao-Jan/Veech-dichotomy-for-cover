module

public import VeechDichotomy.NativeRationalProfiles
public import VeechDichotomy.ShiftedOccupationProfiles

/-! ACTUAL native occupation profiles at rational scales imply the
same limit at varying positive-ratio lengths and shifted intervals.
The profiles supplied by NativeRationalProfiles discharge the only
statistical input; no varying-time genericity oracle is used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeVaryingOccupation

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Set Filter Topology VaryingOccupationProfiles
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem observable_nonneg (B : Set (CompleteOrbits q v)) (x : CompleteOrbits q v) :
    0 ≤ NativeIndicatorMeanProfiles.observable q v B x := by
  by_cases hx : x ∈ B <;> simp [NativeIndicatorMeanProfiles.observable, hx]

theorem varying_average (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (x : CompleteOrbits q v) (m : ℝ)
    (hprof : ∀ (a : PositiveRational) (backward : Bool),
      Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v B) backward ((a.val : ℝ) * R k) x) atTop (𝓝 m))
    (backward : Bool) {T : ℕ → ℝ} {a₀ : ℝ} (ha : Tendsto (fun k => T k / R k) atTop (𝓝 a₀)) (hapos : 0 < a₀) :
    Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v B) backward (T k) x) atTop (𝓝 m) := by
  have hg := NativeIndicatorMeanProfiles.measurable_observable q v hB
  have hbound := NativeIndicatorMeanProfiles.observable_bound q v B
  have hpos := observable_nonneg q v B
  cases backward with
  | false =>
    exact VaryingOccupationProfiles.varying_timeAverage (flow q v) _ hg 1 hbound hpos hR x m
      (fun a => hprof a false) (fun a => hprof a true) ha hapos
  | true =>
    have hdouble : (flow q v).reverse.reverse = flow q v := by ext t y; simp only [Flow.reverse_apply, neg_neg]
    apply VaryingOccupationProfiles.varying_timeAverage (flow q v).reverse _ hg 1 hbound hpos hR x m
      (fun a => hprof a true) _ ha hapos
    intro a
    rw [hdouble]
    exact hprof a false

theorem interval_average (B : Set (CompleteOrbits q v)) (hB : MeasurableSet B)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (x : CompleteOrbits q v) (m : ℝ)
    (hprof : ∀ (a : PositiveRational) (backward : Bool),
      Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v B) backward ((a.val : ℝ) * R k) x) atTop (𝓝 m))
    {A B' : ℕ → ℝ} {a₀ b₀ : ℝ} (hA : Tendsto (fun k => A k / R k) atTop (𝓝 a₀))
    (hB' : Tendsto (fun k => B' k / R k) atTop (𝓝 b₀)) (hab : a₀ < b₀) :
    Tendsto (fun k => (B' k - A k)⁻¹ * ∫ s in A k..B' k, NativeIndicatorMeanProfiles.observable q v B (flow q v s x)) atTop (𝓝 m) :=
  ShiftedOccupationProfiles.interval_average (flow q v) _ (NativeIndicatorMeanProfiles.measurable_observable q v hB) 1
    (NativeIndicatorMeanProfiles.observable_bound q v B) (observable_nonneg q v B) hR x m
    (fun a => hprof a false) (fun a => hprof a true) hA hB' hab

end VeechDichotomy.NativeVaryingOccupation
