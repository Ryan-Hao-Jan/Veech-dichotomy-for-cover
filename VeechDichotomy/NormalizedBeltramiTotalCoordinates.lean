module

public import VeechDichotomy.NormalizedBeltramiTotalInverse

/-! The normalized coordinates themselves are jointly holomorphic on
their actual total-chart source. Forward/inverse identities are literal
identities with the normalized native fiber charts. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NormalizedBeltramiTotalCoordinates

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiDiskData UniformBeltramiDisks BeltramiChartNormalization
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} {b : X} {μ₀ : Parameter} {U : Set X} (D : Data q b μ₀ U)

def forward (z : NativeBeltramiTotalSpace.TotalSpace q) : ℂ × ℂ :=
  (z.point.1.val, scale D.radius * (NativeBeltramiCharts.chart q b z.point).2)

theorem holomorphicAt (z : NativeBeltramiTotalSpace.TotalSpace q)
    (hz : z.point.2 ∈ (NativePowerCharts.chosen q b).chart.source) :
    ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω (forward D) z := by
  have hc : ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω
      (NativeBeltramiTotalSpace.chart q ⟨(μ₀, b)⟩) z :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (⟨(μ₀, b)⟩ : NativeBeltramiTotalSpace.TotalSpace q))
      ((NativeBeltramiCharts.chart_source q b z.point).mpr hz)
  have hscale : ContDiff ℂ ω (fun p : ℂ × ℂ => (p.1, scale D.radius * p.2)) :=
    contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)
  exact (hscale.contMDiff _).comp z hc

theorem forward_value (μ : Near D) (x : NativeBeltramiSurface.Surface q μ.val) :
    forward D ⟨(μ.val, x.point)⟩ = (μ.val.val, normalizedChart D μ x) := rfl

theorem forward_inverse (μ : Near D) {w : ℂ} (hw : ‖w‖ ≤ 2) :
    forward D (NormalizedBeltramiTotalInverse.inverse D (μ.val.val, w)) = (μ.val.val, w) := by
  rw [NormalizedBeltramiTotalInverse.inverse_value]
  change (μ.val.val, normalizedChart D μ ((normalizedChart D μ).symm w)) = _
  rw [(normalizedChart D μ).right_inv ((normalized_closed_target D μ) (by
    simpa only [mem_closedBall, dist_zero_right] using hw))]

theorem inverse_forward (μ : Near D) (x : NativeBeltramiSurface.Surface q μ.val)
    (hx : x ∈ (normalizedChart D μ).source) :
    NormalizedBeltramiTotalInverse.inverse D (forward D ⟨(μ.val, x.point)⟩) = ⟨(μ.val, x.point)⟩ := by
  rw [forward_value, NormalizedBeltramiTotalInverse.inverse_value]
  apply (NativeBeltramiTotalSpace.toProduct q).injective
  refine Prod.ext rfl ?_
  exact congrArg NativeBeltramiSurface.Surface.point ((normalizedChart D μ).left_inv hx)

end VeechDichotomy.NormalizedBeltramiTotalCoordinates
