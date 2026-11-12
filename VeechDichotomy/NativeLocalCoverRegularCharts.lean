module

public import VeechDichotomy.NativeLocalCoverChartContinuity

/-! The jointly continuous pulled regular charts are holomorphic in the
actual relocated source complex structures. Nonzero derivatives follow
from the constructed covering projection, not an assumed family atlas. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLocalCoverRegularCharts

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeLocalCoverFamily
open RelocatedCoverCharts Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) (b : Fin m → X) (hBranch : range b = branchValues π) (T : MarkTransport b)

def localProjection (u : T.neighborhood) (y : RegularPoint π) :
    OpenPartialHomeomorph (Source π b hBranch T u) X :=
  (toOriginal π b hBranch T u).transOpenPartialHomeomorph (localMap π (T.transport u) y)

theorem localProjection_value (u : T.neighborhood) (y : RegularPoint π) (z : Source π b hBranch T u) :
    localProjection π b hBranch T u y z = (cover π b hBranch T u).map z :=
  localMap_apply π (T.transport u) y z.point

theorem localProjection_mdifferentiable (u : T.neighborhood) (y : RegularPoint π) :
    (localProjection π b hBranch T u y).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  apply NativeMovingCoverRegularity.local_chart_holomorphic (cover π b hBranch T u)
    (Homeomorph.refl X) (localProjection π b hBranch T u y)
  · exact fun z _ => localProjection_value π b hBranch T u y z
  · intro z _
    exact (cover π b hBranch T u).holomorphic.mdifferentiableAt (by decide)
  · intro z hz
    apply RelocatedCoverProjection.derivative_ne_zero_regular π (T.transport u) _ _
    exact localMap_source_noncritical π (T.transport u) y hz

def chart (u : T.neighborhood) (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ) :
    OpenPartialHomeomorph (Source π b hBranch T u) ℂ := (localProjection π b hBranch T u y).trans c

theorem chart_mdifferentiable (u : T.neighborhood) (y : RegularPoint π)
    (c : OpenPartialHomeomorph X ℂ) (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) :
    (chart π b hBranch T u y c).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
  (localProjection_mdifferentiable π b hBranch T u y).trans hc

theorem total_chart_value (u : T.neighborhood) (y : RegularPoint π)
    (c : OpenPartialHomeomorph X ℂ) (z : Y) :
    chart π b hBranch T u y c ((toOriginal π b hBranch T u).symm z) =
      (NativeLocalCoverChartContinuity.chart π T y c (u, z)).2 := rfl

end VeechDichotomy.NativeLocalCoverRegularCharts
