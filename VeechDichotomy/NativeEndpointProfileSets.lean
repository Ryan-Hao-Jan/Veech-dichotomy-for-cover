module

public import VeechDichotomy.NativeInvariantOrbitNull
public import VeechDichotomy.NativeRayOccupationMeans

/-! Actual statistical profile sets may be refined to avoid ALL
countably prescribed original transversal endpoints, for both native
area and any tested invariant probability. The already selected
statistical subsequence remains usable. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeEndpointProfileSets

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def Avoids (z : ℕ → X) (x : CompleteOrbits q v) : Prop := ∀ j t, (flow q v t x).val.val ≠ z j

theorem tested_refinement (μ : Measure (CompleteOrbits q v)) (hμ : NativeDynamics.InvariantProbability q v μ)
    (hmin : NativeDynamics.MinimalDirection q v) (z : ℕ → X) (P : CompleteOrbits q v → Prop)
    (hP : ∀ᵐ x ∂μ, P x) : ∀ᵐ x ∂μ, P x ∧ Avoids q v z x :=
  hP.and (NativeInvariantOrbitNull.countable_endpoints q v μ hμ hmin z)

theorem source_refinement (hmin : NativeDynamics.MinimalDirection q v) (z : ℕ → X)
    (P : CompleteOrbits q v → Prop) (E : Set X) (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ a ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = a ∧ P x) :
    ∃ E' : Set X, E' ⊆ E ∧ MNEC.NativePhysicalArea.surfaceArea q E'ᶜ = 0 ∧
      ∀ a ∈ E', ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = a ∧ P x ∧ Avoids q v z x := by
  have hsafe : ∀ᵐ x ∂normalizedCompleteArea q v, Avoids q v z x :=
    NativeInvariantOrbitNull.countable_endpoints q v _ (NativeDynamics.area_invariantProbability q v hmin.1) hmin z
  obtain ⟨S, hS, hSP⟩ := NativeConullSourceSets.conull_source_set q v hmin.1 _ hsafe
  refine ⟨E ∩ S, inter_subset_left, ?_, ?_⟩
  · rw [compl_inter]
    exact measure_union_null hE hS
  · intro a ha
    obtain ⟨x, hxa, hxP⟩ := hEP a ha.1
    obtain ⟨y, hya, hySafe⟩ := hSP a ha.2
    have hxy : x = y := (NativeConullSourceSets.inclusion_measurableEmbedding q v).injective (hxa.trans hya.symm)
    exact ⟨x, hxa, hxP, hxy.symm ▸ hySafe⟩

end VeechDichotomy.NativeEndpointProfileSets
