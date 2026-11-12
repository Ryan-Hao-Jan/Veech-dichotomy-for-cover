module

public import VeechDichotomy.LocalTranslationContinuity
public import VeechDichotomy.ChartHomeomorphExtension

/-! Actual local point transports in a normalized surface chart. Both
maps vary continuously with the target coordinate, fix the complement of
a compact disk, and have literal complex-translation germs at the marks.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PointTransportDisk

open Set Filter Metric Topology LocalTranslationPlane

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

structure Disk where
  center : X
  chart : OpenPartialHomeomorph X ℂ
  center_source : center ∈ chart.source
  chart_center : chart center = 0
  closedBall_target : closedBall 0 2 ⊆ chart.target

namespace Disk

variable (D : Disk (X := X))

def support : Set X := ChartHomeomorphExtension.support D.chart (closedBall 0 2)

theorem support_compact : IsCompact D.support :=
  ChartHomeomorphExtension.support_compact D.chart (isCompact_closedBall _ _) D.closedBall_target

theorem plane_fixed (δ : Parameter) (z : ℂ) (hz : z ∉ closedBall (0 : ℂ) 2) :
    LocalTranslationPlane.homeomorph δ z = z := by
  have hn : ¬ ‖z‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hz
  exact homeomorph_fixed δ (le_of_lt (lt_of_not_ge hn))

theorem parameter_target (δ : Parameter) : δ.val ∈ D.chart.target := by
  apply D.closedBall_target
  rw [mem_closedBall, dist_zero_right]
  have h := δ.property
  linarith

variable [T2Space X]

def transport (δ : Parameter) : X ≃ₜ X :=
  ChartHomeomorphExtension.homeomorph D.chart (isCompact_closedBall _ _) D.closedBall_target
    LocalTranslationPlane.homeomorph
    (fun δ _ hz => LocalTranslationContinuity.preserves_target δ D.closedBall_target hz)
    (fun δ _ hz => LocalTranslationContinuity.inverse_preserves_target δ D.closedBall_target hz)
    plane_fixed LocalTranslationContinuity.continuous_forward LocalTranslationContinuity.continuous_inverse δ

theorem transport_apply_of_source (δ : Parameter) {x : X} (hx : x ∈ D.chart.source) :
    D.transport δ x = D.chart.symm (LocalTranslationPlane.homeomorph δ (D.chart x)) := by
  change ChartHomeomorphExtension.value D.chart (LocalTranslationPlane.homeomorph δ) x = _
  rw [ChartHomeomorphExtension.value, ite_eq_left hx]

theorem transport_symm_apply_of_source (δ : Parameter) {x : X} (hx : x ∈ D.chart.source) :
    (D.transport δ).symm x = D.chart.symm ((LocalTranslationPlane.homeomorph δ).symm (D.chart x)) := by
  change ChartHomeomorphExtension.value D.chart (LocalTranslationPlane.homeomorph δ).symm x = _
  rw [ChartHomeomorphExtension.value, ite_eq_left hx]

theorem transport_fixed (δ : Parameter) {x : X} (hx : x ∉ D.support) : D.transport δ x = x :=
  ChartHomeomorphExtension.value_fixed D.chart (LocalTranslationPlane.homeomorph δ) (plane_fixed δ) hx

theorem transport_inverse_fixed (δ : Parameter) {x : X} (hx : x ∉ D.support) : (D.transport δ).symm x = x := by
  have h := (D.transport δ).symm_apply_apply x
  rwa [D.transport_fixed δ hx] at h

theorem continuous_transport : Continuous (fun p : Parameter × X => D.transport p.1 p.2) :=
  ChartHomeomorphExtension.continuous_value D.chart (isCompact_closedBall _ _) D.closedBall_target
    LocalTranslationPlane.homeomorph
    (fun δ _ hz => LocalTranslationContinuity.preserves_target δ D.closedBall_target hz)
    plane_fixed LocalTranslationContinuity.continuous_forward

theorem continuous_transport_inverse : Continuous (fun p : Parameter × X => (D.transport p.1).symm p.2) :=
  ChartHomeomorphExtension.continuous_value D.chart (isCompact_closedBall _ _) D.closedBall_target
    (fun δ => (LocalTranslationPlane.homeomorph δ).symm)
    (fun δ _ hz => LocalTranslationContinuity.inverse_preserves_target δ D.closedBall_target hz)
    (fun δ _ hz => ChartHomeomorphExtension.inverse_fixed (LocalTranslationPlane.homeomorph δ) (plane_fixed δ) hz)
    LocalTranslationContinuity.continuous_inverse

theorem transport_center (δ : Parameter) : D.transport δ D.center = D.chart.symm δ.val := by
  rw [D.transport_apply_of_source δ D.center_source, D.chart_center, homeomorph_origin]

theorem translation_germ (δ : Parameter) :
    ∀ᶠ x in 𝓝 D.center, D.transport δ x = D.chart.symm (D.chart x + δ.val) := by
  have hball : ball (0 : ℂ) 1 ∈ 𝓝 (D.chart D.center) := by
    rw [D.chart_center]
    exact ball_mem_nhds _ (by norm_num)
  have hnear := (D.chart.continuousAt D.center_source) hball
  filter_upwards [D.chart.open_source.mem_nhds D.center_source, hnear] with x hx hxB
  have hn : ‖D.chart x‖ ≤ 1 := by
    have hlt : ‖D.chart x‖ < 1 := by simpa only [mem_preimage, mem_ball, dist_zero_right] using hxB
    exact hlt.le
  rw [D.transport_apply_of_source δ hx, homeomorph_apply, move_translation hn]

theorem inverse_translation_germ (δ : Parameter) :
    ∀ᶠ x in 𝓝 (D.chart.symm δ.val),
      (D.transport δ).symm x = D.chart.symm (D.chart x - δ.val) := by
  have hb : D.chart.symm δ.val ∈ D.chart.source := D.chart.map_target (D.parameter_target δ)
  have ht : Tendsto D.chart (𝓝 (D.chart.symm δ.val)) (𝓝 δ.val) := by
    simpa only [D.chart.right_inv (D.parameter_target δ)] using (D.chart.continuousAt hb).tendsto
  have hnear := ht (LocalTranslationContinuity.inverse_translation_germ δ)
  filter_upwards [D.chart.open_source.mem_nhds hb, hnear] with x hx hplane
  rw [D.transport_symm_apply_of_source δ hx, hplane]

theorem moves_center_to {x : X} (hx : x ∈ D.chart.source) (hn : ‖D.chart x‖ < 1 / 2) :
    D.transport ⟨D.chart x, hn⟩ D.center = x := by
  rw [D.transport_center]
  exact D.chart.left_inv hx

end Disk
end VeechDichotomy.PointTransportDisk
