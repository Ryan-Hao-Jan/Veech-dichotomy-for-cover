module

public import VeechDichotomy.NativeVariableSourceProfiles
public import VeechDichotomy.NativeRayReferenceTimes

/-! ACTUAL inverse-contraction source clocks, including clocks shifted
by converging ray times, have the occupation means supplied by the
constructed stable profiles. Genuine area-conull/test-a.e. profile sets
are constructed for any actual diverging native ray-time sequence. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRayOccupationMeans

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Set Filter Topology
open NativeVariableSourceProfiles NativeRayReferenceTimes
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane) (hv : v ≠ 0)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

include hv in
theorem average_of_height (B : Set (CompleteOrbits q v)) (t : ℕ → ℝ) (x : CompleteOrbits q v) (m : ℝ)
    (hs : StableProfile q v B (fun k => reference v (t k)) x m) (backward : Bool)
    {H : ℕ → ℝ} {H₀ : ℝ} (hH : Tendsto H atTop (𝓝 H₀)) (hH₀ : 0 < H₀) :
    Tendsto (fun k => NativeContinuousMeanProfiles.average q v (NativeIndicatorMeanProfiles.observable q v B) backward
      (H k / NativeTeichmullerRay.contraction v (t k)) x) atTop (𝓝 m) :=
  hs.1 backward _ H₀ (lifted_ratio_tendsto v hv t H hH) hH₀

include hv in
theorem shifted_interval (B : Set (CompleteOrbits q v)) (t : ℕ → ℝ) (x : CompleteOrbits q v) (m : ℝ)
    (hs : StableProfile q v B (fun k => reference v (t k)) x m)
    {L U : ℕ → ℝ} {L₀ U₀ : ℝ} (hL : Tendsto L atTop (𝓝 L₀)) (hU : Tendsto U atTop (𝓝 U₀)) (hLU : L₀ < U₀) :
    Tendsto (fun k => ((U k / NativeTeichmullerRay.contraction v (t k)) - (L k / NativeTeichmullerRay.contraction v (t k)))⁻¹ *
      ∫ s in (L k / NativeTeichmullerRay.contraction v (t k))..(U k / NativeTeichmullerRay.contraction v (t k)),
        NativeIndicatorMeanProfiles.observable q v B (flow q v s x)) atTop (𝓝 m) :=
  hs.2 _ _ L₀ U₀ (lifted_ratio_tendsto v hv t L hL) (lifted_ratio_tendsto v hv t U hU) hLU

theorem source_and_test (ν : Measure (CompleteOrbits q v)) (hν : NativeDynamics.InvariantProbability q v ν)
    (B : ℕ → Set (CompleteOrbits q v)) (hB : ∀ j, MeasurableSet (B j)) (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ E : Set X, MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0 ∧
      (∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ ∀ j,
        StableProfile q v (B j) (fun k => reference v (t (σ k))) x
          (NativeIndicatorMeanProfiles.mean q v (normalizedCompleteArea q v) (NativeDynamics.area_invariantProbability q v hv) (B j) (hB j) false x)) ∧
      (∀ᵐ x ∂ν, ∀ j, StableProfile q v (B j) (fun k => reference v (t (σ k))) x
        (NativeIndicatorMeanProfiles.mean q v ν hν (B j) (hB j) false x)) :=
  NativeVariableSourceProfiles.source_and_test q v hv ν hν B hB (fun k => reference v (t k)) (reference_tendsto v hv ht)

end VeechDichotomy.NativeRayOccupationMeans
