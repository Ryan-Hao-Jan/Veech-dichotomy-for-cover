module

public import VeechDichotomy.NativeFlowboxDwellSets
public import VeechDichotomy.NativeIndicatorMeanProfiles

/-! The statistical flowbox observable is the actual indicator of the
native open box. Its time integral equals the Lebesgue dwell time, so
the proved crossing estimate applies directly to occupation averages. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFlowboxOccupation

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeVerticalFlowboxes NativeFlowboxDwellSets
open Set MeasureTheory Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def phaseBox (l r b h : ℝ) : Set (CompleteOrbits q vertical) :=
  Subtype.val ⁻¹' box q i l r b h

theorem phaseBox_open (l r b h : ℝ) : IsOpen (phaseBox q i l r b h) :=
  (box_open q i l r b h).preimage continuous_subtype_val

theorem observable_eq_indicator (x : CompleteOrbits q vertical) (l r b h : ℝ) :
    (fun s => NativeIndicatorMeanProfiles.observable q vertical (phaseBox q i l r b h)
      (flow q vertical s x)) = (occupancy q i x l r b h).indicator (fun _ => (1 : ℝ)) := by
  funext s
  by_cases hs : s ∈ occupancy q i x l r b h
  · have hy : flow q vertical s x ∈ phaseBox q i l r b h := hs
    simp [NativeIndicatorMeanProfiles.observable, hs, hy]
  · have hy : flow q vertical s x ∉ phaseBox q i l r b h := hs
    simp [NativeIndicatorMeanProfiles.observable, hs, hy]

theorem integral_eq_dwell (x : CompleteOrbits q vertical) (l r b h a z : ℝ) (haz : a ≤ z) :
    (∫ s in a..z, NativeIndicatorMeanProfiles.observable q vertical (phaseBox q i l r b h)
      (flow q vertical s x)) = volume.real (occupancy q i x l r b h ∩ Ioc a z) := by
  rw [observable_eq_indicator, intervalIntegral.integral_of_le haz,
    setIntegral_indicator (occupancy_open q i x l r b h).measurableSet, setIntegral_const]
  simp [inter_comm]

theorem integral_count_error {l0 r0 b0 u0 l r b h : ℝ}
    (hh : 0 < h) (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) {a z : ℝ} (haz : a ≤ z) :
    |(∫ s in a..z, NativeIndicatorMeanProfiles.observable q vertical (phaseBox q i l r b h)
      (flow q vertical s x)) -
      h * (SeparatedWindowCounts.count (hitTimes q i x l r b) a z : ℝ)| ≤ h := by
  rw [integral_eq_dwell q i x l r b h a z haz]
  exact dwell_error q i hh hl hr hb hu hR x a z

end VeechDichotomy.NativeFlowboxOccupation
