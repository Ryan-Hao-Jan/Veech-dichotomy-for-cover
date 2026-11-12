module

public import VeechDichotomy.NativeBeltramiMarkedSections
public import VeechDichotomy.NativeBeltramiCoverCoordinates

/-! Actual uniform chart neighborhoods along a marked deformation
section. For nearby complex parameters, one fixed closed coordinate disk
lies in the chart target and its inverse stays in a prescribed OLD open
neighborhood. This includes marks at differential zeros. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiNeighborhoods

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem uniform_target (q : Differential X) (b : X) (μ₀ : Parameter) {U : Set X}
    (hU : IsOpen U) (hb : b ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ r : ℝ, 0 < r ∧ ∀ μ : Parameter, dist μ.val μ₀.val < ε →
      ∀ z : ℂ, ‖z‖ ≤ r → (μ.val, z) ∈ (NativeBeltramiCharts.chart q b).target ∧
        ((NativeBeltramiCharts.chart q b).symm (μ.val, z)).2 ∈ U := by
  let e := NativeBeltramiCharts.chart q b
  let W : Set (ℂ × ℂ) := e.target ∩ e.symm ⁻¹' (univ ×ˢ U)
  have hW : IsOpen W := e.symm.continuousOn.isOpen_inter_preimage e.open_target (isOpen_univ.prod hU)
  have hp : (μ₀.val, 0) ∈ W := by
    refine ⟨?_, ?_⟩
    · have h := e.map_source (NativeBeltramiCharts.chart_center q b μ₀)
      rwa [NativeBeltramiCoverCoordinates.source_center_value (ωY := q) b μ₀] at h
    · change e.symm (μ₀.val, 0) ∈ univ ×ˢ U
      rw [NativeBeltramiCoverCoordinates.source_inverse_center (ωY := q) b μ₀]
      exact ⟨mem_univ μ₀, hb⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hp)
  refine ⟨δ / 2, half_pos hδ, δ / 2, half_pos hδ, ?_⟩
  intro μ hμ z hz
  have hpball : (μ.val, z) ∈ ball (μ₀.val, (0 : ℂ)) δ := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨hμ.trans (half_lt_self hδ), ?_⟩
    rw [dist_zero_right]
    exact hz.trans_lt (half_lt_self hδ)
  have hw := hball hpball
  exact ⟨hw.1, hw.2.2⟩

end VeechDichotomy.UniformBeltramiNeighborhoods
