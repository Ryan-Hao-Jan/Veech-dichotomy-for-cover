module

public import VeechDichotomy.NativeBeltramiCoverBranchValues

/-! The literal covering map between the constructed complex total
families. Its joint continuity, parameter commutation and actual fiber
restrictions are derived from the original parameter/surface topology. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeBeltramiCoverTotalMap

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}
variable (π : Cover ωX ωY)

def underlying (p : Parameter × Y) : Parameter × X := (p.1, π.map p.2)

theorem continuous_underlying : Continuous (underlying π) :=
  continuous_fst.prodMk (π.holomorphic.continuous.comp continuous_snd)

def map (p : NativeBeltramiTotalSpace.TotalSpace ωY) : NativeBeltramiTotalSpace.TotalSpace ωX := ⟨underlying π p.point⟩

theorem continuous_map : Continuous (map π) :=
  (NativeBeltramiTotalSpace.toProduct ωX).symm.continuous.comp
    ((continuous_underlying π).comp (NativeBeltramiTotalSpace.toProduct ωY).continuous)

theorem projection_map (p : NativeBeltramiTotalSpace.TotalSpace ωY) :
    NativeBeltramiTotalSpace.projection ωX (map π p) = NativeBeltramiTotalSpace.projection ωY p := rfl

theorem map_section (y : Y) (μ : Parameter) :
    map π (NativeBeltramiMarkedSections.sectionMap ωY y μ) = NativeBeltramiMarkedSections.sectionMap ωX (π.map y) μ := rfl

theorem map_fiber (μ : Parameter) (y : NativeBeltramiSurface.Surface ωY μ) :
    map π (NativeBeltramiFibers.inclusion ωY μ y) = NativeBeltramiFibers.inclusion ωX μ ((NativeBeltramiCover.cover π μ).map y) := rfl

theorem surjective_map : Function.Surjective (map π) := by
  intro x
  obtain ⟨y, hy⟩ := π.surjective x.point.2
  refine ⟨⟨(x.point.1, y)⟩, ?_⟩
  apply (NativeBeltramiTotalSpace.toProduct ωX).injective
  exact Prod.ext rfl hy

theorem finite_fibers (x : NativeBeltramiTotalSpace.TotalSpace ωX) : (map π ⁻¹' {x}).Finite := by
  apply ((π.finite_fibers x.point.2).image (fun y => (NativeBeltramiTotalSpace.toProduct ωY).symm (x.point.1, y))).subset
  intro y hy
  have hμ : y.point.1 = x.point.1 := congrArg (fun z : NativeBeltramiTotalSpace.TotalSpace ωX => z.point.1) hy
  have hpoint : π.map y.point.2 = x.point.2 := congrArg (fun z : NativeBeltramiTotalSpace.TotalSpace ωX => z.point.2) hy
  refine ⟨y.point.2, hpoint, ?_⟩
  apply (NativeBeltramiTotalSpace.toProduct ωY).injective
  exact Prod.ext hμ.symm rfl

end VeechDichotomy.NativeBeltramiCoverTotalMap
