module

public import VeechDichotomy.NativeConullSourceSets

/-! A property carried by genuine complete representatives of an actual
raw-area conull source set holds almost everywhere on the actual normalized
complete phase. This is the converse of the existing source-set transfer. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeConullPhaseProperties

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Set
open scoped Manifold ContDiff ENNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem ae_phase (hv : v ≠ 0) (P : CompleteOrbits q v → Prop)
    (hP : ∀ᵐ z ∂MNEC.NativePhysicalArea.surfaceArea q,
      ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ P x) :
    ∀ᵐ x ∂normalizedCompleteArea q v, P x := by
  have hraw := hP
  rw [← (NativeConullSourceSets.surface_inclusion_measurePreserving q v hv).map_eq,
    (NativeConullSourceSets.inclusion_measurableEmbedding q v).ae_map_iff] at hraw
  have hphase : ∀ᵐ x ∂completeArea q v, P x := by
    filter_upwards [hraw] with x hx
    obtain ⟨y, hyx, hyP⟩ := hx
    have heq : y = x := (NativeConullSourceSets.inclusion_measurableEmbedding q v).injective hyx
    exact heq ▸ hyP
  exact (Measure.ae_ennreal_smul_measure_iff
    (ENNReal.inv_ne_zero.mpr (MNEC.NativeFiniteRegularArea.regularArea_univ_ne_top q))).mpr hphase

theorem of_conull_set (hv : v ≠ 0) (P : CompleteOrbits q v → Prop) (E : Set X)
    (hE : MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0)
    (hEP : ∀ z ∈ E, ∃ x : CompleteOrbits q v, NativeConullSourceSets.inclusion q v x = z ∧ P x) :
    ∀ᵐ x ∂normalizedCompleteArea q v, P x := by
  apply ae_phase q v hv P
  have hs : ∀ᵐ z ∂MNEC.NativePhysicalArea.surfaceArea q, z ∈ E := ae_iff.mpr hE
  exact hs.mono hEP

end VeechDichotomy.NativeConullPhaseProperties
