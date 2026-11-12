module

public import VeechDichotomy.NativeBufferedFlowboxes
public import VeechDichotomy.PlaneRectangleMeasureExt

/-! Actual measurable coordinate embeddings on concrete complete-phase
flowboxes. Pushing the genuine restricted measure into the plane records
its clipped rectangle masses and determines its entire restriction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBufferedFlowboxes.Data

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeCompleteDirectionalFlow
open MeasureTheory Set NativePrimitiveRectangles
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} (D : NativeBufferedFlowboxes.Data q)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def baseCoordinate (x : D.phaseRegion) : Plane := chart q D.index x.val.val

theorem baseCoordinate_embedding : MeasurableEmbedding D.baseCoordinate := by
  have hinc : MeasurableEmbedding (fun x : D.phaseRegion => (x.val.val : Regular q)) :=
    (MeasurableEmbedding.subtype_coe (completeOrbitSet_measurable q vertical)).comp
      (MeasurableEmbedding.subtype_coe D.phaseRegion_open.measurableSet)
  have hj := PlaneRectangleMeasureExt.codRestrict_embedding hinc (chart q D.index).source
    (fun x => x.property.1)
  exact (chart q D.index).isOpenEmbedding_restrict.measurableEmbedding.comp hj

def coordinateMeasure (μ : Measure (CompleteOrbits q vertical)) : Measure Plane :=
  (μ.comap (Subtype.val : D.phaseRegion → CompleteOrbits q vertical)).map D.baseCoordinate

theorem coordinateMeasure_apply (μ : Measure (CompleteOrbits q vertical)) (A : Set Plane) :
    D.coordinateMeasure μ A = μ (D.phaseRegion ∩ {x | chart q D.index x.val ∈ A}) := by
  rw [coordinateMeasure, D.baseCoordinate_embedding.map_apply,
    comap_subtype_coe_apply D.phaseRegion_open.measurableSet]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩

theorem restrict_eq_of_coordinate_eq (μ ν : Measure (CompleteOrbits q vertical))
    (h : D.coordinateMeasure μ = D.coordinateMeasure ν) : μ.restrict D.phaseRegion = ν.restrict D.phaseRegion := by
  have hsub := D.baseCoordinate_embedding.map_injective h
  have hmap := congrArg (fun ρ : Measure D.phaseRegion => ρ.map (Subtype.val : D.phaseRegion → CompleteOrbits q vertical)) hsub
  simpa only [map_comap_subtype_coe D.phaseRegion_open.measurableSet] using hmap

end VeechDichotomy.NativeBufferedFlowboxes.Data
