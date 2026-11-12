module

public import VeechDichotomy.PointTransportDisk
public import VeechDichotomy.NativePowerCharts
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Normalized point-transport disks are constructed in arbitrary open
neighborhoods of native curve points. The actual chart is holomorphic in
both directions, so the transport and inverse are holomorphic near the
old and moved marks, including marks at zeros of the differential. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePointTransportDisk

open MNEC.NativeAbelianDifferential Set Filter Metric Topology PointTransportDisk
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem exists_disk (q : Differential X) (a : X) {U : Set X} (hU : IsOpen U) (haU : a ∈ U) :
    ∃ D : Disk (X := X), D.center = a ∧ D.support ⊆ U ∧ D.chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  let p := NativePowerCharts.chosen q a
  have h0T : (0 : ℂ) ∈ p.chart.target := by rw [← p.center_zero]; exact p.chart.map_source p.center
  have hinv : p.chart.symm 0 = a := by rw [← p.center_zero]; exact p.chart.left_inv p.center
  have hi : Tendsto p.chart.symm (𝓝 (0 : ℂ)) (𝓝 a) := by
    simpa only [p.center_zero, hinv] using (p.chart.symm.continuousAt (p.chart.map_source p.center)).tendsto
  have hnear : p.chart.target ∩ p.chart.symm ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    inter_mem (p.chart.open_target.mem_nhds h0T) (hi (hU.mem_nhds haU))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : closedBall (0 : ℂ) r ⊆ p.chart.target ∩ p.chart.symm ⁻¹' U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hball
  let c : ℂ := 2 / (r : ℂ)
  have hc : c ≠ 0 := div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hr.ne')
  let H := Homeomorph.mulLeft₀ c hc
  let e := p.chart.transHomeomorph H
  have hcinv : ‖c⁻¹‖ = r / 2 := by
    dsimp only [c]
    rw [inv_div, norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    norm_num
  have hscale {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 2) : c⁻¹ * z ∈ closedBall (0 : ℂ) r := by
    have hn : ‖z‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [mem_closedBall, dist_zero_right, norm_mul, hcinv]
    calc
      r / 2 * ‖z‖ ≤ r / 2 * 2 := mul_le_mul_of_nonneg_left hn (half_pos hr).le
      _ = r := by ring
  have heT : closedBall (0 : ℂ) 2 ⊆ e.target := by
    intro z hz
    change c⁻¹ * z ∈ p.chart.target
    exact (hclosed (hscale hz)).1
  have hMul : H.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    constructor
    · intro z _
      change MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℂ => c * w) univ z
      exact (hasDerivAt_const_mul c).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
    · intro z _
      change MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℂ => c⁻¹ * w) univ z
      exact (hasDerivAt_const_mul c⁻¹).differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  have heHol : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
    dsimp only [e]
    rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
    exact p.mdifferentiable.trans hMul
  let D : Disk (X := X) :=
    { center := a
      chart := e
      center_source := p.center
      chart_center := by change c * p.chart a = 0; rw [p.center_zero, mul_zero]
      closedBall_target := heT }
  refine ⟨D, rfl, ?_, heHol⟩
  rintro _ ⟨z, hz, rfl⟩
  change p.chart.symm (c⁻¹ * z) ∈ U
  exact (hclosed (hscale hz)).2

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem mdifferentiable_near_of_chart_germ (e : OpenPartialHomeomorph X ℂ)
    (he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (F : X → X) (x : X) (hx : x ∈ e.source)
    (a : ℂ) (harg : e x + a ∈ e.target)
    (hgerm : ∀ᶠ y in 𝓝 x, F y = e.symm (e y + a)) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F y := by
  let V : Set X := e.source ∩ e ⁻¹' (fun z : ℂ => z + a) ⁻¹' e.target
  have hV : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source
    (e.open_target.preimage (continuous_id.add continuous_const))
  have hxV : x ∈ V := ⟨hx, harg⟩
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hgerm
  filter_upwards [(hW.inter hV).mem_nhds ⟨hxW, hxV⟩] with y hy
  have hsrc := he.mdifferentiableAt hy.2.1
  have hadd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : ℂ => z + a) (e y) :=
    (differentiableAt_id.add_const a).mdifferentiableAt
  have hInv := he.mdifferentiableAt_symm hy.2.2
  apply (hInv.comp y (hadd.comp y hsrc)).congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hy.1] with z hz
  exact hWsub hz

omit [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem transport_holomorphic_near (D : Disk (X := X))
    (hD : D.chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (δ : LocalTranslationPlane.Parameter) :
    ∀ᶠ x in 𝓝 D.center, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (D.transport δ) x := by
  apply mdifferentiable_near_of_chart_germ D.chart hD (D.transport δ) D.center D.center_source δ.val
  · rw [D.chart_center, zero_add]
    exact D.parameter_target δ
  · exact D.translation_germ δ

omit [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
theorem transport_inverse_holomorphic_near (D : Disk (X := X))
    (hD : D.chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (δ : LocalTranslationPlane.Parameter) :
    ∀ᶠ x in 𝓝 (D.chart.symm δ.val), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (D.transport δ).symm x := by
  apply mdifferentiable_near_of_chart_germ D.chart hD (D.transport δ).symm (D.chart.symm δ.val)
    (D.chart.map_target (D.parameter_target δ)) (-δ.val)
  · rw [D.chart.right_inv (D.parameter_target δ), add_neg_cancel]
    rw [← D.chart_center]
    exact D.chart.map_source D.center_source
  · simpa only [sub_eq_add_neg] using D.inverse_translation_germ δ

end VeechDichotomy.NativePointTransportDisk
