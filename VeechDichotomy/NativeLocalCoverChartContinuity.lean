module

public import VeechDichotomy.ParameterizedCoverChart
public import VeechDichotomy.NativeLocalCoverFamily

/-! Joint topological chart control on the actual moving source family.
At every noncritical old point the reference local covering neighborhood
is fixed; a fixed base chart gives one total open chart for all parameters
where its target condition holds. This is stronger than continuity of
the underlying projections, without asserting ambient moduli continuity. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLocalCoverChartContinuity

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
variable (π : Cover ωX ωY) {b : Fin m → X} (T : MarkTransport b)

def chart (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ) :
    OpenPartialHomeomorph (T.neighborhood × Y) (T.neighborhood × ℂ) :=
  ParameterizedCoverChart.chart T.transport T.continuous_transport T.continuous_inverse (oldLocalMap π y) c

theorem projection_formula (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ)
    (p : T.neighborhood × Y) : (chart π T y c p).2 = c (T.transport p.1 (π.map p.2)) := by
  have h := localMap_apply π (T.transport p.1) y p.2
  exact congrArg c h

theorem inverse_formula (y : RegularPoint π) (c : OpenPartialHomeomorph X ℂ)
    (p : T.neighborhood × ℂ) :
    (chart π T y c).symm p = (p.1, (oldLocalMap π y).symm ((T.transport p.1).symm (c.symm p.2))) := rfl

theorem center_mem_source (y : RegularPoint π) (u : T.neighborhood) (c : OpenPartialHomeomorph X ℂ)
    (hc : T.transport u (π.map y.val) ∈ c.source) : (u, y.val) ∈ (chart π T y c).source := by
  apply (ParameterizedCoverChart.mem_source_iff _ _ _ _ _ _).mpr
  refine ⟨localMap_center π (T.transport u) y, ?_⟩
  change localMap π (T.transport u) y y.val ∈ c.source
  rw [localMap_apply]
  exact hc

end VeechDichotomy.NativeLocalCoverChartContinuity
