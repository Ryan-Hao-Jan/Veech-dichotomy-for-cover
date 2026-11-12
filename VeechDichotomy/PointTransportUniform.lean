module

public import VeechDichotomy.NativePointTransportDisk
public import VeechDichotomy.DisjointPointTransport

/-! The actual cutoff transports are biholomorphic on fixed inner disks,
uniformly for all displacement parameters. These fixed neighborhoods allow
critical charts to be chosen without shrinking separately at every parameter. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PointTransportUniform

open Set Filter Metric Topology PointTransportDisk LocalTranslationPlane
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem plane_inverse_translation_germ (δ : Parameter) {w : ℂ} (hw : ‖w‖ < 1) :
    ∀ᶠ z in 𝓝 (LocalTranslationPlane.homeomorph δ w),
      (LocalTranslationPlane.homeomorph δ).symm z = z - δ.val := by
  have hball : ball (0 : ℂ) 1 ∈ 𝓝 ((LocalTranslationPlane.homeomorph δ).symm
      (LocalTranslationPlane.homeomorph δ w)) := by
    rw [Homeomorph.symm_apply_apply]
    exact isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hw)
  have hnear := (LocalTranslationPlane.homeomorph δ).symm.continuous.continuousAt hball
  filter_upwards [hnear] with z hz
  have hn : ‖(LocalTranslationPlane.homeomorph δ).symm z‖ ≤ 1 :=
    (by simpa only [mem_preimage, mem_ball, dist_zero_right] using hz :
      ‖(LocalTranslationPlane.homeomorph δ).symm z‖ < 1).le
  apply (eq_sub_iff_add_eq).mpr
  exact (move_translation hn δ.val).symm.trans
    ((LocalTranslationPlane.homeomorph δ).apply_symm_apply z)

variable {X : Type*} [TopologicalSpace X]

def innerDisk (D : Disk (X := X)) : Set X := D.chart.source ∩ D.chart ⁻¹' ball (0 : ℂ) 1

theorem innerDisk_open (D : Disk (X := X)) : IsOpen (innerDisk D) :=
  D.chart.continuousOn.isOpen_inter_preimage D.chart.open_source isOpen_ball

theorem center_mem_innerDisk (D : Disk (X := X)) : D.center ∈ innerDisk D := by
  refine ⟨D.center_source, ?_⟩
  simp only [mem_preimage, mem_ball, D.chart_center, dist_self]
  norm_num

theorem innerDisk_norm (D : Disk (X := X)) {x : X} (hx : x ∈ innerDisk D) : ‖D.chart x‖ < 1 := by
  simpa only [mem_preimage, mem_ball, dist_zero_right] using hx.2

variable [T2Space X]

theorem translation_germ (D : Disk (X := X)) (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    ∀ᶠ z in 𝓝 x, D.transport δ z = D.chart.symm (D.chart z + δ.val) := by
  filter_upwards [(innerDisk_open D).mem_nhds hx] with z hz
  rw [D.transport_apply_of_source δ hz.1, homeomorph_apply, move_translation (innerDisk_norm D hz).le]

omit [T2Space X] in
theorem translated_target (D : Disk (X := X)) (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    D.chart x + δ.val ∈ D.chart.target := by
  apply D.closedBall_target
  rw [mem_closedBall, dist_zero_right]
  have hδ := δ.property
  have hxNorm := innerDisk_norm D hx
  exact (norm_add_le _ _).trans (by linarith)

theorem transport_value (D : Disk (X := X)) (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    D.transport δ x = D.chart.symm (D.chart x + δ.val) :=
  (translation_germ D δ hx).self_of_nhds

theorem transport_source (D : Disk (X := X)) (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    D.transport δ x ∈ D.chart.source := by
  rw [transport_value D δ hx]
  exact D.chart.map_target (translated_target D δ hx)

theorem transport_coordinate (D : Disk (X := X)) (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    D.chart (D.transport δ x) = D.chart x + δ.val := by
  rw [transport_value D δ hx, D.chart.right_inv (translated_target D δ hx)]

theorem inverse_translation_germ (D : Disk (X := X)) (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    ∀ᶠ z in 𝓝 (D.transport δ x), (D.transport δ).symm z = D.chart.symm (D.chart z - δ.val) := by
  have hplane := plane_inverse_translation_germ δ (innerDisk_norm D hx)
  have hcoord : D.chart (D.transport δ x) = LocalTranslationPlane.homeomorph δ (D.chart x) := by
    rw [transport_coordinate D δ hx, homeomorph_apply, move_translation (innerDisk_norm D hx).le]
  have hnear : ∀ᶠ z in 𝓝 (D.transport δ x),
      (LocalTranslationPlane.homeomorph δ).symm (D.chart z) = D.chart z - δ.val := by
    have hp : ∀ᶠ z in 𝓝 (D.chart (D.transport δ x)),
        (LocalTranslationPlane.homeomorph δ).symm z = z - δ.val := by rwa [hcoord]
    exact (D.chart.continuousAt (transport_source D δ hx)) hp
  filter_upwards [D.chart.open_source.mem_nhds (transport_source D δ hx), hnear] with z hz hformula
  rw [D.transport_symm_apply_of_source δ hz, hformula]

variable [ChartedSpace ℂ X]

theorem holomorphic_at (D : Disk (X := X)) (hD : D.chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (D.transport δ) x :=
  (NativePointTransportDisk.mdifferentiable_near_of_chart_germ D.chart hD
    (D.transport δ) x hx.1 δ.val (translated_target D δ hx) (translation_germ D δ hx)).self_of_nhds

theorem inverse_holomorphic_at (D : Disk (X := X)) (hD : D.chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (δ : Parameter) {x : X} (hx : x ∈ innerDisk D) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (D.transport δ).symm (D.transport δ x) := by
  apply Filter.Eventually.self_of_nhds
  apply NativePointTransportDisk.mdifferentiable_near_of_chart_germ D.chart hD
    (D.transport δ).symm (D.transport δ x) (transport_source D δ hx) (-δ.val)
  · rw [transport_coordinate D δ hx, add_neg_cancel_right]
    exact D.chart.map_source hx.1
  · simpa only [sub_eq_add_neg] using inverse_translation_germ D δ hx

end VeechDichotomy.PointTransportUniform
