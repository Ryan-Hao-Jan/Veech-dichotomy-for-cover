module

public import VeechDichotomy.NativeFlowboxOccupation
public import VeechDichotomy.BoundedDwellRates
public import VeechDichotomy.PositiveRatioLengths
public import VeechDichotomy.NativeProfileSubsequences

/-! Actual native occupation profiles imply actual transversal crossing
rates on every interval whose endpoints have separated limiting ratios
to the reference clock. The resulting rate is the box mean divided by height. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFlowboxCrossingRates

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeVerticalFlowboxes NativeFlowboxOccupation
open Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem of_interval_average {l0 r0 b0 u0 l r b h : ℝ}
    (hh : 0 < h) (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) {A B : ℕ → ℝ} {m : ℝ}
    (hL : Tendsto (fun k => B k - A k) atTop atTop)
    (havg : Tendsto (fun k => (B k - A k)⁻¹ *
      ∫ s in A k..B k, NativeIndicatorMeanProfiles.observable q vertical (phaseBox q i l r b h)
        (flow q vertical s x)) atTop (𝓝 m)) :
    Tendsto (fun k => (SeparatedWindowCounts.count (hitTimes q i x l r b) (A k) (B k) : ℝ) /
      (B k - A k)) atTop (𝓝 (m / h)) := by
  apply BoundedDwellRates.crossing_rate hh.ne' h hL
  · filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    exact integral_count_error q i hh hl hr hb hu hR x (by linarith)
  · simpa only [div_eq_mul_inv, mul_comm] using havg

theorem of_stable_profile {l0 r0 b0 u0 l r b h : ℝ}
    (hh : 0 < h) (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) (R : ℕ → ℝ) (hclock : Tendsto R atTop atTop) {m : ℝ}
    (hprof : NativeVariableSourceProfiles.StableProfile q vertical (phaseBox q i l r b h) R x m)
    {A B : ℕ → ℝ} {a₀ b₀ : ℝ} (hA : Tendsto (fun k => A k / R k) atTop (𝓝 a₀))
    (hB : Tendsto (fun k => B k / R k) atTop (𝓝 b₀)) (hab : a₀ < b₀) :
    Tendsto (fun k => (SeparatedWindowCounts.count (hitTimes q i x l r b) (A k) (B k) : ℝ) /
      (B k - A k)) atTop (𝓝 (m / h)) :=
  of_interval_average q i hh hl hr hb hu hR x (PositiveRatioLengths.interval_divergent hclock hA hB hab)
    (hprof.2 A B a₀ b₀ hA hB hab)

end VeechDichotomy.NativeFlowboxCrossingRates
