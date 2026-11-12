module

public import VeechDichotomy.PointTransportUniform

/-! Fixed inner disks for the combined disjoint transports. Their literal
single-disk restrictions give biholomorphicity for every parameter. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DisjointPointTransportUniform

open Set Filter Metric Topology PointTransportDisk LocalTranslationPlane
open DisjointPointTransport PointTransportUniform
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

theorem holomorphic_at (D : ι → Disk (X := X))
    (hD : ∀ i, (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (F : (ι → Parameter) → X ≃ₜ X)
    (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)
    (δ : ι → Parameter) (i : ι) {x : X} (hx : x ∈ innerDisk (D i)) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F δ) x := by
  have hsup := support_mem_nhds (D i) hx.1 (lt_trans (innerDisk_norm (D i) hx) (by norm_num))
  apply (PointTransportUniform.holomorphic_at (D i) (hD i) (δ i) hx).congr_of_eventuallyEq
  filter_upwards [hsup] with z hz
  exact hown i δ z hz

theorem inverse_holomorphic_at (D : ι → Disk (X := X))
    (hD : ∀ i, (D i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (F : (ι → Parameter) → X ≃ₜ X)
    (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)
    (δ : ι → Parameter) (i : ι) {x : X} (hx : x ∈ innerDisk (D i)) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F δ).symm (F δ x) := by
  have hsup := support_mem_nhds (D i) hx.1 (lt_trans (innerDisk_norm (D i) hx) (by norm_num))
  rw [hown i δ x (mem_of_mem_nhds hsup)]
  have hnorm : ‖(D i).chart ((D i).transport (δ i) x)‖ < 2 := by
    rw [transport_coordinate (D i) (δ i) hx]
    have hδ := (δ i).property
    have hxn := innerDisk_norm (D i) hx
    exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)
  have hsupNew := support_mem_nhds (D i) (transport_source (D i) (δ i) hx) hnorm
  apply (PointTransportUniform.inverse_holomorphic_at (D i) (hD i) (δ i) hx).congr_of_eventuallyEq
  filter_upwards [hsupNew] with z hz
  exact inverse_restriction D F hown δ i hz

end VeechDichotomy.DisjointPointTransportUniform
