module

public import VeechDichotomy.UniformBeltramiDiskData
public import VeechDichotomy.PointTransportDisk

/-! Explicit actual normalized transport disks in every nearby native
deformed fiber, with one fixed old compact support. The inverse-coordinate
bound is uniform and will control the whole transport construction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiDisks

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open BeltramiChartNormalization UniformBeltramiDiskData
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} {b : X} {μ₀ : Parameter} {U : Set X} (D : Data q b μ₀ U)

abbrev Near := {μ : Parameter // dist μ.val μ₀.val < D.epsilon}

def normalizedPlane (μ : Near D) : ℂ ≃ₜ ℂ := plane q b D.radius D.radius_pos μ.val

def normalizedChart (μ : Near D) : OpenPartialHomeomorph (NativeBeltramiSurface.Surface q μ.val) ℂ :=
  BeltramiChartNormalization.chart q b D.radius D.radius_pos μ.val

theorem rescaled_target (μ : Near D) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    (scale D.radius)⁻¹ * z ∈ (NativeBeltramiSurface.chart q μ.val ⟨b⟩).target := by
  have ht := (NativeBeltramiCharts.chart_target q b (μ.val.val, (scale D.radius)⁻¹ * z)).mp
    (D.raw_target μ.val μ.property _ (inverse_scale_bound D.radius_pos hz))
  have hp : BeltramiParameter.chart.symm μ.val.val = μ.val := BeltramiParameter.chart.left_inv (mem_univ μ.val)
  rw [hp] at ht
  exact ht.2

theorem normalized_closed_target (μ : Near D) : closedBall 0 2 ⊆ (normalizedChart D μ).target := by
  intro z hz
  change (scale D.radius)⁻¹ * z ∈ (NativeBeltramiSurface.chart q μ.val ⟨b⟩).target
  exact rescaled_target D μ (by simpa only [mem_closedBall, dist_zero_right] using hz)

def disk (μ : Near D) : PointTransportDisk.Disk (X := NativeBeltramiSurface.Surface q μ.val) where
  center := ⟨b⟩
  chart := normalizedChart D μ
  center_source := BeltramiChartNormalization.chart_center q b D.radius D.radius_pos μ.val
  chart_center := BeltramiChartNormalization.chart_center_zero q b D.radius D.radius_pos μ.val
  closedBall_target := normalized_closed_target D μ

theorem disk_holomorphic (μ : Near D) : (disk D μ).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
  BeltramiChartNormalization.chart_mdifferentiable q b D.radius D.radius_pos μ.val

theorem normalized_inverse_value (μ : Near D) (z : ℂ) :
    ((normalizedChart D μ).symm z).point =
      ((NativeBeltramiCharts.chart q b).symm (μ.val.val, (scale D.radius)⁻¹ * z)).2 := by
  rw [NativeBeltramiSurface.inverse_value q μ.val (⟨b⟩ : NativeBeltramiSurface.Surface q μ.val)]
  rfl

theorem inverse_plane_bound (μ : Near D) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖(normalizedPlane D μ).symm z‖ < D.oldRadius := by
  have ht := rescaled_target D μ hz
  have htOld : (normalizedPlane D μ).symm z ∈ (NativePowerCharts.chosen q b).chart.target := ht
  have hc := D.inverse_control μ.val μ.property ((scale D.radius)⁻¹ * z) (inverse_scale_bound D.radius_pos hz)
  have hvalue : ((NativeBeltramiCharts.chart q b).symm (μ.val.val, (scale D.radius)⁻¹ * z)).2 =
      (NativePowerCharts.chosen q b).chart.symm ((normalizedPlane D μ).symm z) := by
    rw [← normalized_inverse_value]
    exact BeltramiChartNormalization.chart_inverse_point q b D.radius D.radius_pos μ.val z
  rw [hvalue, (NativePowerCharts.chosen q b).chart.right_inv htOld] at hc
  exact hc.2

theorem disk_support (μ : Near D) :
    (NativeBeltramiSurface.toOriginal q μ.val) '' (disk D μ).support ⊆
      (NativePowerCharts.chosen q b).chart.symm '' closedBall 0 D.oldRadius := by
  rintro _ ⟨x, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨(normalizedPlane D μ).symm z, ?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    exact (inverse_plane_bound D μ (by simpa only [mem_closedBall, dist_zero_right] using hz)).le
  · exact (BeltramiChartNormalization.chart_inverse_point q b D.radius D.radius_pos μ.val z).symm

theorem disk_support_subset (μ : Near D) :
    (NativeBeltramiSurface.toOriginal q μ.val) '' (disk D μ).support ⊆ U :=
  (disk_support D μ).trans D.old_support

end VeechDichotomy.UniformBeltramiDisks
