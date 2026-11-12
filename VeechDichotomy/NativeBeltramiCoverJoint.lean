module

public import VeechDichotomy.NativeBeltramiCoverCoordinates
public import VeechDichotomy.PowerRootBidisk

/-! The actual covering map BETWEEN the complex total families is
jointly holomorphic, including every zero and ramification section.
The local monomial is derived from actual power identities and analytic
order. Properness follows from the constructed proper parameter projection. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCoverJoint

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeBeltramiCoverTotalMap
open NativeBeltramiCoverCoordinates BeltramiPlane Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY)

theorem coordinate_holomorphic (y : Y) (μ : Parameter) :
    ContDiffAt ℂ ω (coordinateMap π y) (μ.val, 0) := by
  have hscalar := PowerRootBidisk.contDiffAt_of_power_germ (coordinateScalar π y) μ.val
    (NativePowerCharts.chosen ωX (π.map y)).exponent_pos (NativePowerCharts.chosen ωY y).exponent_pos
    (coordinate_continuous_near π y μ) (coordinate_power_germ π y μ) (slice_analytic π y μ)
  have hpair : ContDiffAt ℂ ω (fun p : ℂ × ℂ => (p.1, coordinateScalar π y p)) (μ.val, 0) :=
    contDiffAt_fst.prodMk hscalar
  apply hpair.congr_of_eventuallyEq
  filter_upwards [(NativeBeltramiCharts.chart ωY y).open_target.mem_nhds (domain_center π y μ).1] with p hp
  exact Prod.ext (coordinate_first π y hp) rfl

theorem holomorphic_map : ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (map π) := by
  intro z
  rw [contMDiffAt_iff]
  refine ⟨(continuous_map π).continuousAt, ?_⟩
  have hrange : range (𝓘(ℂ, ℂ × ℂ) : ModelWithCorners ℂ (ℂ × ℂ) (ℂ × ℂ)) = univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange, contDiffWithinAt_univ]
  have hfun : (extChartAt 𝓘(ℂ, ℂ × ℂ) (map π z) ∘ map π ∘ (extChartAt 𝓘(ℂ, ℂ × ℂ) z).symm) =
      coordinateMap π z.point.2 := by
    funext p
    rfl
  have hbase : extChartAt 𝓘(ℂ, ℂ × ℂ) z z = (z.point.1.val, 0) :=
    source_center_value (ωY := ωY) z.point.2 z.point.1
  rw [hfun, hbase]
  exact coordinate_holomorphic π z.point.2 z.point.1

theorem proper_map : IsProperMap (map π) :=
  isProperMap_of_comp_of_t2 (continuous_map π) (NativeBeltramiTotalSpace.proper_projection ωX).continuous
    (show IsProperMap (NativeBeltramiTotalSpace.projection ωX ∘ map π) from NativeBeltramiTotalSpace.proper_projection ωY)

end VeechDichotomy.NativeBeltramiCoverJoint
