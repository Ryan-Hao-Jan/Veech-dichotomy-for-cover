module

public import VeechDichotomy.UniformBeltramiNeighborhoods
public import VeechDichotomy.BeltramiChartNormalization

/-! Constructed uniform disk data. Both the old compact coordinate
support and the new normalized chart radius are fixed independently of
the nearby deformation parameter. Existence is proved from actual chart
inverse continuity and the checked uniform target theorem. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiDiskData

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

structure Data (q : Differential X) (b : X) (μ₀ : Parameter) (U : Set X) where
  oldRadius : ℝ
  oldRadius_pos : 0 < oldRadius
  old_target : closedBall 0 oldRadius ⊆ (NativePowerCharts.chosen q b).chart.target
  old_support : (NativePowerCharts.chosen q b).chart.symm '' closedBall 0 oldRadius ⊆ U
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  radius : ℝ
  radius_pos : 0 < radius
  raw_target : ∀ μ : Parameter, dist μ.val μ₀.val < epsilon → ∀ z : ℂ, ‖z‖ ≤ radius →
    (μ.val, z) ∈ (NativeBeltramiCharts.chart q b).target
  inverse_control : ∀ μ : Parameter, dist μ.val μ₀.val < epsilon → ∀ z : ℂ, ‖z‖ ≤ radius →
    ((NativeBeltramiCharts.chart q b).symm (μ.val, z)).2 ∈ (NativePowerCharts.chosen q b).chart.source ∧
      ‖(NativePowerCharts.chosen q b).chart ((NativeBeltramiCharts.chart q b).symm (μ.val, z)).2‖ < oldRadius

theorem nonempty_data (q : Differential X) (b : X) (μ₀ : Parameter) {U : Set X}
    (hU : IsOpen U) (hb : b ∈ U) : Nonempty (Data q b μ₀ U) := by
  let p := NativePowerCharts.chosen q b
  have h0 : (0 : ℂ) ∈ p.chart.target := by rw [← p.center_zero]; exact p.chart.map_source p.center
  have hInv0 : p.chart.symm 0 = b := by rw [← p.center_zero]; exact p.chart.left_inv p.center
  have hi : Tendsto p.chart.symm (𝓝 (0 : ℂ)) (𝓝 b) := by
    simpa only [hInv0] using (p.chart.symm.continuousAt h0).tendsto
  have hnear : p.chart.target ∩ p.chart.symm ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    inter_mem (p.chart.open_target.mem_nhds h0) (hi (hU.mem_nhds hb))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let s := R / 2
  have hs : 0 < s := half_pos hR
  have hclosed : closedBall (0 : ℂ) s ⊆ p.chart.target ∩ p.chart.symm ⁻¹' U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hball
  let V : Set X := p.chart.source ∩ p.chart ⁻¹' ball (0 : ℂ) s
  have hV : IsOpen V := p.chart.continuousOn.isOpen_inter_preimage p.chart.open_source isOpen_ball
  have hbV : b ∈ V := ⟨p.center, by rw [mem_preimage, p.center_zero]; exact mem_ball_self hs⟩
  obtain ⟨ε, hε, r, hr, htarget⟩ := UniformBeltramiNeighborhoods.uniform_target q b μ₀ hV hbV
  refine ⟨{ oldRadius := s
            oldRadius_pos := hs
            old_target := fun _ hz => (hclosed hz).1
            old_support := ?_
            epsilon := ε
            epsilon_pos := hε
            radius := r
            radius_pos := hr
            raw_target := fun μ hμ z hz => (htarget μ hμ z hz).1
            inverse_control := ?_ }⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hclosed hz).2
  · intro μ hμ z hz
    have hv := (htarget μ hμ z hz).2
    refine ⟨hv.1, ?_⟩
    simpa only [mem_preimage, mem_ball, dist_zero_right] using hv.2

def chosenData (q : Differential X) (b : X) (μ₀ : Parameter) {U : Set X} (hU : IsOpen U) (hb : b ∈ U) : Data q b μ₀ U :=
  Classical.choice (nonempty_data q b μ₀ hU hb)

end VeechDichotomy.UniformBeltramiDiskData
