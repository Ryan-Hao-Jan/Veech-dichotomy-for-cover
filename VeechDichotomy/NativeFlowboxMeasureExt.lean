module

public import VeechDichotomy.NativeFlowboxSubrectangles
public import VeechDichotomy.NativeCountableFlowboxBasis

/-! Actual complete native phase measures are determined by concrete
buffered flowboxes. Coordinate rectangle uniqueness determines each
restriction, and a proved countable flowbox cover determines the measure.
No measure-determining property is assumed for an arbitrary basis. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeFlowboxMeasureExt

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow MeasureTheory Set Topology
open NativePrimitiveRectangles NativeBufferedFlowboxes
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem restrict_eq (μ ν : Measure (CompleteOrbits q vertical)) [IsFiniteMeasure μ]
    (h : ∀ D : Data q, μ D.phaseRegion = ν D.phaseRegion) (D : Data q) :
    μ.restrict D.phaseRegion = ν.restrict D.phaseRegion := by
  have : IsFiniteMeasure (D.coordinateMeasure μ) := by
    unfold Data.coordinateMeasure
    infer_instance
  apply D.restrict_eq_of_coordinate_eq μ ν
  apply PlaneRectangleMeasureExt.ext
  intro l r b t
  rw [D.coordinateMeasure_apply, D.coordinateMeasure_apply]
  change μ (D.phaseRegion ∩ {x | MNEC.NativePrimitiveAreaCharts.chart q D.index x.val ∈ rectangle l r b t}) =
    ν (D.phaseRegion ∩ {x | MNEC.NativePrimitiveAreaCharts.chart q D.index x.val ∈ rectangle l r b t})
  rcases D.clipped_or_empty l r b t with hempty | ⟨E, hE⟩
  · simp only [hempty, measure_empty]
  · rw [← hE]
    exact h E

theorem ext (μ ν : Measure (CompleteOrbits q vertical)) [IsFiniteMeasure μ]
    (h : ∀ D : Data q, μ D.phaseRegion = ν D.phaseRegion) : μ = ν := by
  obtain ⟨D, hD⟩ := NativeCountableFlowboxBasis.exists_countable_basis q
  have hphase := NativeCountableFlowboxBasis.phase_basis q D hD
  have hcover : ⋃ n, (D n).phaseRegion = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨U, ⟨n, rfl⟩, hx, _⟩ := hphase.exists_subset_of_mem_open (mem_univ x) isOpen_univ
    exact ⟨n, hx⟩
  exact Measure.ext_of_iUnion_eq_univ hcover (fun n => restrict_eq q μ ν h (D n))

end VeechDichotomy.NativeFlowboxMeasureExt
