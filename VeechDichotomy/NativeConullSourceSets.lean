module

public import VeechDichotomy.NativeDynamics
public import MNEC.NativePhysicalArea

/-! Almost-everywhere properties on the actual normalized complete
native phase give conull sets of ORIGINAL surface points with genuine
complete-phase representatives. Actual AE completeness, measured
inclusions and finite nonzero area discharge the transfer. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeConullSourceSets

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MNEC.NativeCompleteDirectionalArea MeasureTheory Set Filter Topology
open scoped Manifold ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (v : Plane)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def inclusion (x : CompleteOrbits q v) : X := x.val.val

theorem inclusion_measurableEmbedding : MeasurableEmbedding (inclusion q v) :=
  (MeasurableEmbedding.subtype_coe (regularSet_open q).measurableSet).comp
    (MeasurableEmbedding.subtype_coe (completeOrbitSet_measurable q v))

theorem surface_inclusion_measurePreserving (hv : v ≠ 0) :
    MeasurePreserving (inclusion q v) (completeArea q v) (MNEC.NativePhysicalArea.surfaceArea q) := by
  have hc := complete_inclusion_measurePreserving q v
  have hrestrict := Measure.restrict_eq_self_of_ae_mem (MNEC.NativeConullDirectionalOrbits.ae_complete q v hv)
  rw [hrestrict] at hc
  exact (MNEC.NativePhysicalArea.regular_inclusion_measurePreserving q).comp hc

theorem ae_surface (hv : v ≠ 0) (P : CompleteOrbits q v → Prop)
    (hP : ∀ᵐ x ∂normalizedCompleteArea q v, P x) :
    ∀ᵐ z ∂MNEC.NativePhysicalArea.surfaceArea q, ∃ x : CompleteOrbits q v, inclusion q v x = z ∧ P x := by
  have hdenom : (MNEC.NativeRegularArea.regularArea q univ)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (MNEC.NativeFiniteRegularArea.regularArea_univ_ne_top q)
  have hraw : ∀ᵐ x ∂completeArea q v, P x := (Measure.ae_ennreal_smul_measure_iff hdenom).mp hP
  rw [← (surface_inclusion_measurePreserving q v hv).map_eq, (inclusion_measurableEmbedding q v).ae_map_iff]
  filter_upwards [hraw] with x hx
  exact ⟨x, rfl, hx⟩

theorem conull_source_set (hv : v ≠ 0) (P : CompleteOrbits q v → Prop)
    (hP : ∀ᵐ x ∂normalizedCompleteArea q v, P x) :
    ∃ E : Set X, MNEC.NativePhysicalArea.surfaceArea q Eᶜ = 0 ∧
      ∀ z ∈ E, ∃ x : CompleteOrbits q v, inclusion q v x = z ∧ P x := by
  have hs := ae_surface q v hv P hP
  exact ⟨{z | ∃ x : CompleteOrbits q v, inclusion q v x = z ∧ P x}, ae_iff.mp hs, fun _ hz => hz⟩

end VeechDichotomy.NativeConullSourceSets
