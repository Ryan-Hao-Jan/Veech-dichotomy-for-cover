module

public import VeechDichotomy.NativeBufferedFlowboxes
public import VeechDichotomy.NativeEndpointProfileSets

/-! Every countable family of actual buffered native boxes has common
source-area and tested-measure crossing profiles on one subsequence.
The source set is genuinely conull in the original surface; the tested
measure may be singular. All variable interval profiles hold pointwise. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFlowboxProfileSets

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea
open NativePrimitiveRectangles NativeBufferedFlowboxes Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def Safe (D : Data q) (x : CompleteOrbits q vertical) : Prop :=
  (∀ t, (flow q vertical t x).val.val ≠ NativeClosedBaseHits.endpoint q D.index D.left D.bottom) ∧
  (∀ t, (flow q vertical t x).val.val ≠ NativeClosedBaseHits.endpoint q D.index D.right D.bottom)

def CrossingProfile (D : Data q) (R : ℕ → ℝ) (x : CompleteOrbits q vertical) (m : ℝ) : Prop :=
  ∀ (A B : ℕ → ℝ) (a b : ℝ), Tendsto (fun k => A k / R k) atTop (𝓝 a) →
    Tendsto (fun k => B k / R k) atTop (𝓝 b) → a < b →
      Tendsto (fun k => (SeparatedWindowCounts.count (D.closedHits x) (A k) (B k) : ℝ) /
        (B k - A k)) atTop (𝓝 (m / D.height))

def FullProfile (D : Data q) (R : ℕ → ℝ) (x : CompleteOrbits q vertical) (m : ℝ) : Prop :=
  NativeVariableSourceProfiles.StableProfile q vertical D.phaseRegion R x m ∧
    Safe q D x ∧ CrossingProfile q D R x m

theorem crossing_of_safe (D : Data q) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (x : CompleteOrbits q vertical) (m : ℝ)
    (hp : NativeVariableSourceProfiles.StableProfile q vertical D.phaseRegion R x m) (hs : Safe q D x) :
    CrossingProfile q D R x m := by
  intro A B a b hA hB hab
  exact D.closed_crossing_rate x R hR hp hs.1 hs.2 hA hB hab

theorem subsequence (D : Data q) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (x : CompleteOrbits q vertical) (m : ℝ) (hp : FullProfile q D R x m)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) : FullProfile q D (R ∘ σ) x m := by
  have hs := NativeProfileSubsequences.subsequence q vertical D.phaseRegion D.phaseRegion_open.measurableSet
    R hR x m hp.1 σ hσ
  exact ⟨hs, hp.2.1, crossing_of_safe q D (R ∘ σ) (hR.comp hσ.tendsto_atTop) x m hs hp.2.1⟩

theorem safe_ae (μ : Measure (CompleteOrbits q vertical)) (hμ : NativeDynamics.InvariantProbability q vertical μ)
    (hmin : NativeDynamics.MinimalDirection q vertical) (D : ℕ → Data q) :
    ∀ᵐ x ∂μ, ∀ j, Safe q (D j) x := by
  apply ae_all_iff.mpr
  intro j
  exact (NativeInvariantOrbitNull.endpoint_avoid q vertical μ hμ hmin
    (NativeClosedBaseHits.endpoint q (D j).index (D j).left (D j).bottom)).and
    (NativeInvariantOrbitNull.endpoint_avoid q vertical μ hμ hmin
      (NativeClosedBaseHits.endpoint q (D j).index (D j).right (D j).bottom))

theorem source_and_test (hmin : NativeDynamics.MinimalDirection q vertical)
    (ν : Measure (CompleteOrbits q vertical)) (hν : NativeDynamics.InvariantProbability q vertical ν)
    (D : ℕ → Data q) (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ E : Set X, MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0 ∧
      (∀ z ∈ E, ∃ x : CompleteOrbits q vertical, NativeConullSourceSets.inclusion q vertical x = z ∧ ∀ j,
        FullProfile q (D j) (R ∘ σ) x
          (NativeIndicatorMeanProfiles.mean q vertical (normalizedCompleteArea q vertical)
            (NativeDynamics.area_invariantProbability q vertical hmin.1) (D j).phaseRegion
            (D j).phaseRegion_open.measurableSet false x)) ∧
      (∀ᵐ x ∂ν, ∀ j, FullProfile q (D j) (R ∘ σ) x
        (NativeIndicatorMeanProfiles.mean q vertical ν hν (D j).phaseRegion
          (D j).phaseRegion_open.measurableSet false x)) := by
  obtain ⟨σ, hσ, E, hE, harea, htest⟩ := NativeVariableSourceProfiles.source_and_test q vertical hmin.1 ν hν
    (fun j => (D j).phaseRegion) (fun j => (D j).phaseRegion_open.measurableSet) R hR
  have hRσ : Tendsto (R ∘ σ) atTop atTop := hR.comp hσ.tendsto_atTop
  have hsarea := safe_ae q _ (NativeDynamics.area_invariantProbability q vertical hmin.1) hmin D
  obtain ⟨S, hS, hsafe⟩ := NativeConullSourceSets.conull_source_set q vertical hmin.1 _ hsarea
  refine ⟨σ, hσ, E ∩ S, ?_, ?_, ?_⟩
  · rw [compl_inter]
    exact measure_union_null hE hS
  · intro z hz
    obtain ⟨x, hxz, hxp⟩ := harea z hz.1
    obtain ⟨y, hyz, hys⟩ := hsafe z hz.2
    have hxy : x = y := (NativeConullSourceSets.inclusion_measurableEmbedding q vertical).injective (hxz.trans hyz.symm)
    refine ⟨x, hxz, fun j => ?_⟩
    have hxs : Safe q (D j) x := hxy.symm ▸ hys j
    exact ⟨hxp j, hxs, crossing_of_safe q (D j) (R ∘ σ) hRσ x _ (hxp j) hxs⟩
  · filter_upwards [htest, safe_ae q ν hν hmin D] with x hxp hxs
    exact fun j => ⟨hxp j, hxs j, crossing_of_safe q (D j) (R ∘ σ) hRσ x _ (hxp j) (hxs j)⟩

end VeechDichotomy.NativeFlowboxProfileSets
