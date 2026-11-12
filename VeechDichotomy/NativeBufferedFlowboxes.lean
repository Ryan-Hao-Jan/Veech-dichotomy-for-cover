module

public import VeechDichotomy.NativeFlowboxCrossingRates
public import VeechDichotomy.NativeClosedBaseHits

/-! Concrete buffered native primitive boxes. The data only records
actual chart coordinates, positive dimensions and rectangle containment.
All dynamics and crossing estimates are derived by the preceding proofs. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBufferedFlowboxes

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

structure Data (q : Differential X) where
  index : Index q
  (left right bottom height outerLeft outerRight outerBottom outerTop : ℝ)
  width_pos : left < right
  height_pos : 0 < height
  left_buffer : outerLeft < left
  right_buffer : right < outerRight
  bottom_buffer : outerBottom < bottom
  top_buffer : bottom + height < outerTop
  target : rectangle outerLeft outerRight outerBottom outerTop ⊆ (chart q index).target

namespace Data

variable {q : Differential X} (D : Data q)

def region : Set (Regular q) := NativeVerticalFlowboxes.box q D.index D.left D.right D.bottom D.height
def phaseRegion : Set (CompleteOrbits q vertical) :=
  NativeFlowboxOccupation.phaseBox q D.index D.left D.right D.bottom D.height
def hits (x : CompleteOrbits q vertical) : Set ℝ :=
  NativeVerticalFlowboxes.hitTimes q D.index x D.left D.right D.bottom
def closedHits (x : CompleteOrbits q vertical) : Set ℝ :=
  NativeClosedBaseHits.closedHitTimes q D.index x D.left D.right D.bottom

theorem region_open : IsOpen D.region := NativeVerticalFlowboxes.box_open q D.index _ _ _ _
theorem phaseRegion_open : IsOpen D.phaseRegion := NativeFlowboxOccupation.phaseBox_open q D.index _ _ _ _

theorem separated_hits (x : CompleteOrbits q vertical) :
    SeparatedWindowCounts.Separated D.height (D.hits x) :=
  NativeVerticalFlowboxes.separated_hits q D.index D.left_buffer.le D.right_buffer.le
    D.bottom_buffer D.top_buffer D.target x

theorem finite_hits (x : CompleteOrbits q vertical) (a b : ℝ) : (D.hits x ∩ Icc a b).Finite :=
  SeparatedWindowCounts.finite_window D.height_pos (D.separated_hits x) a b

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem crossing_rate (x : CompleteOrbits q vertical) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) {m : ℝ}
    (hp : NativeVariableSourceProfiles.StableProfile q vertical D.phaseRegion R x m)
    {A B : ℕ → ℝ} {a b : ℝ} (hA : Tendsto (fun k => A k / R k) atTop (𝓝 a))
    (hB : Tendsto (fun k => B k / R k) atTop (𝓝 b)) (hab : a < b) :
    Tendsto (fun k => (SeparatedWindowCounts.count (D.hits x) (A k) (B k) : ℝ) /
      (B k - A k)) atTop (𝓝 (m / D.height)) :=
  NativeFlowboxCrossingRates.of_stable_profile q D.index D.height_pos D.left_buffer.le D.right_buffer.le
    D.bottom_buffer D.top_buffer D.target x R hR hp hA hB hab

theorem closed_crossing_rate (x : CompleteOrbits q vertical) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) {m : ℝ}
    (hp : NativeVariableSourceProfiles.StableProfile q vertical D.phaseRegion R x m)
    (hleft : ∀ t, (flow q vertical t x).val.val ≠ NativeClosedBaseHits.endpoint q D.index D.left D.bottom)
    (hright : ∀ t, (flow q vertical t x).val.val ≠ NativeClosedBaseHits.endpoint q D.index D.right D.bottom)
    {A B : ℕ → ℝ} {a b : ℝ} (hA : Tendsto (fun k => A k / R k) atTop (𝓝 a))
    (hB : Tendsto (fun k => B k / R k) atTop (𝓝 b)) (hab : a < b) :
    Tendsto (fun k => (SeparatedWindowCounts.count (D.closedHits x) (A k) (B k) : ℝ) /
      (B k - A k)) atTop (𝓝 (m / D.height)) := by
  have heq : D.hits x = D.closedHits x :=
    NativeClosedBaseHits.hitTimes_eq_closed q D.index x D.left D.right D.bottom hleft hright
  rw [← heq]
  exact D.crossing_rate x R hR hp hA hB hab

end Data

end VeechDichotomy.NativeBufferedFlowboxes
