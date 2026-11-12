module

public import VeechDichotomy.NativeVerticalFlowboxes
public import VeechDichotomy.NativeInvariantOrbitNull

/-! Open and closed native transversals have identical hit sets for
orbits avoiding the two actual endpoints. Minimality supplies that
avoidance almost everywhere for every tested invariant probability. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeClosedBaseHits

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles NativeVerticalFlowboxes Set MeasureTheory Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def closedBase (l r b : ℝ) : Set (Regular q) :=
  {y | y ∈ (chart q i).source ∧ (chart q i y).1 ∈ Icc l r ∧ (chart q i y).2 = b}

def closedHitTimes (x : CompleteOrbits q vertical) (l r b : ℝ) : Set ℝ :=
  {s | (timeMap q vertical s x).val ∈ closedBase q i l r b}

def endpoint (c b : ℝ) : X := ((chart q i).symm (c, b)).val

theorem point_eq_endpoint {c b : ℝ} {y : Regular q} (hy : y ∈ (chart q i).source)
    (hx : (chart q i y).1 = c) (hz : (chart q i y).2 = b) :
    y.val = endpoint q i c b := by
  have hp : chart q i y = (c, b) := Prod.ext hx hz
  have heq : y = (chart q i).symm (c, b) := by rw [← hp, (chart q i).left_inv hy]
  exact congrArg Subtype.val heq

theorem hitTimes_eq_closed (x : CompleteOrbits q vertical) (l r b : ℝ)
    (hleft : ∀ t, (flow q vertical t x).val.val ≠ endpoint q i l b)
    (hright : ∀ t, (flow q vertical t x).val.val ≠ endpoint q i r b) :
    hitTimes q i x l r b = closedHitTimes q i x l r b := by
  ext s
  constructor
  · intro hs
    exact ⟨hs.1, ⟨hs.2.1.1.le, hs.2.1.2.le⟩, hs.2.2⟩
  · intro hs
    refine ⟨hs.1, ⟨?_, ?_⟩, hs.2.2⟩
    · by_contra hlt
      have hx : (chart q i (timeMap q vertical s x).val).1 = l :=
        le_antisymm (le_of_not_gt hlt) hs.2.1.1
      exact hleft s (point_eq_endpoint q i hs.1 hx hs.2.2)
    · by_contra hlt
      have hx : (chart q i (timeMap q vertical s x).val).1 = r :=
        le_antisymm hs.2.1.2 (le_of_not_gt hlt)
      exact hright s (point_eq_endpoint q i hs.1 hx hs.2.2)

theorem ae_hitTimes_eq_closed (μ : Measure (CompleteOrbits q vertical))
    (hμ : NativeDynamics.InvariantProbability q vertical μ)
    (hmin : NativeDynamics.MinimalDirection q vertical) (l r b : ℝ) :
    ∀ᵐ x ∂μ, hitTimes q i x l r b = closedHitTimes q i x l r b := by
  filter_upwards [NativeInvariantOrbitNull.endpoint_avoid q vertical μ hμ hmin (endpoint q i l b),
    NativeInvariantOrbitNull.endpoint_avoid q vertical μ hμ hmin (endpoint q i r b)] with x hx hy
  exact hitTimes_eq_closed q i x l r b hx hy

end VeechDichotomy.NativeClosedBaseHits
