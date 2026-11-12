module

public import VeechDichotomy.NativeBeltramiSurface
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.GroupWithZero

/-! Explicit normalized fiber charts, built from ONE fixed original
power chart and the jointly continuous unit-disk power lifts. The scale
is constant in the deformation parameter. No varying chart choice occurs. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiChartNormalization

open MNEC.NativeAbelianDifferential BeltramiPlane Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

def scale (r : ℝ) : ℂ := 2 / (r : ℂ)

theorem scale_ne_zero {r : ℝ} (hr : 0 < r) : scale r ≠ 0 :=
  div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hr.ne')

theorem inverse_scale_norm {r : ℝ} (hr : 0 < r) : ‖(scale r)⁻¹‖ = r / 2 := by
  rw [scale, inv_div, norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  norm_num

theorem inverse_scale_bound {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ 2) : ‖(scale r)⁻¹ * z‖ ≤ r := by
  rw [norm_mul, inverse_scale_norm hr]
  calc
    r / 2 * ‖z‖ ≤ r / 2 * 2 := mul_le_mul_of_nonneg_left hz (half_pos hr).le
    _ = r := by ring

theorem mulLeft_mdifferentiable (c : ℂ) (hc : c ≠ 0) :
    (Homeomorph.mulLeft₀ c hc).toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  constructor
  · intro z _
    change MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℂ => c * w) univ z
    exact (hasDerivAt_const_mul c).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  · intro z _
    change MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℂ => c⁻¹ * w) univ z
    exact (hasDerivAt_const_mul c⁻¹).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (b : X) (r : ℝ) (hr : 0 < r)

def plane (μ : Parameter) : ℂ ≃ₜ ℂ :=
  (BeltramiPowerLift.rootHomeomorph μ (NativePowerCharts.chosen q b).exponent (NativePowerCharts.chosen q b).exponent_pos).trans
    (Homeomorph.mulLeft₀ (scale r) (scale_ne_zero hr))

theorem plane_zero (μ : Parameter) : plane q b r hr μ 0 = 0 := by
  change scale r * BeltramiPowerLift.rootHomeomorph μ _ _ 0 = 0
  rw [BeltramiPowerLift.rootHomeomorph_zero, mul_zero]

theorem continuous_plane : Continuous (fun p : Parameter × ℂ => plane q b r hr p.1 p.2) :=
  continuous_const.mul (BeltramiPowerLift.continuous_forward (NativePowerCharts.chosen q b).exponent_pos)

theorem continuous_plane_inverse : Continuous (fun p : Parameter × ℂ => (plane q b r hr p.1).symm p.2) :=
  (BeltramiPowerLift.continuous_inverse (NativePowerCharts.chosen q b).exponent_pos).comp
    (continuous_fst.prodMk (continuous_const.mul continuous_snd))

def chart (μ : Parameter) : OpenPartialHomeomorph (NativeBeltramiSurface.Surface q μ) ℂ :=
  (NativeBeltramiSurface.chart q μ ⟨b⟩).transHomeomorph (Homeomorph.mulLeft₀ (scale r) (scale_ne_zero hr))

theorem chart_source (μ : Parameter) (x : NativeBeltramiSurface.Surface q μ) :
    x ∈ (chart q b r hr μ).source ↔ x.point ∈ (NativePowerCharts.chosen q b).chart.source := Iff.rfl

theorem chart_center (μ : Parameter) : (⟨b⟩ : NativeBeltramiSurface.Surface q μ) ∈ (chart q b r hr μ).source :=
  NativeBeltramiSurface.chart_center q μ ⟨b⟩

theorem chart_center_zero (μ : Parameter) : chart q b r hr μ ⟨b⟩ = 0 := by
  change scale r * NativeBeltramiSurface.chart q μ ⟨b⟩ ⟨b⟩ = 0
  rw [NativeBeltramiSurface.chart_center_zero, mul_zero]

theorem chart_forward (μ : Parameter) (x : X) :
    chart q b r hr μ ((NativeBeltramiSurface.toOriginal q μ).symm x) =
      plane q b r hr μ ((NativePowerCharts.chosen q b).chart x) := rfl

theorem chart_inverse_point (μ : Parameter) (z : ℂ) :
    ((chart q b r hr μ).symm z).point = (NativePowerCharts.chosen q b).chart.symm ((plane q b r hr μ).symm z) := rfl

theorem chart_mdifferentiable (μ : Parameter) : (chart q b r hr μ).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  rw [chart, OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ)) (chart_mem_atlas ℂ (⟨b⟩ : NativeBeltramiSurface.Surface q μ))).trans
    (mulLeft_mdifferentiable (scale r) (scale_ne_zero hr))

end VeechDichotomy.BeltramiChartNormalization
