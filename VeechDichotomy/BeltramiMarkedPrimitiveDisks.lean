module

public import VeechDichotomy.BeltramiMarkedUniformPrimitiveEscape

/-! Every actual limit-fiber point, including a zero, has a fixed
source-coordinate disk in an actual native power-primitive domain.
Thus the uniform nearby-fiber escape bound can be instantiated at ANY
limit point, rather than assuming a preselected primitive neighborhood. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedPrimitiveDisks

open MNEC.NativeAbelianDifferential NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem exists_disk (p₀ : Base A) (y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2) :
    ∃ j : X, ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.closedBall
      (BeltramiMarkedScaledSlices.chart π F hBranch (p₀.2, y₀.point) p₀ y₀) r,
      (p₀, z) ∈ BeltramiMarkedUniformPrimitiveBounds.domain π F hBranch (p₀.2, y₀.point) j := by
  let s : ComplexBeltramiMarkParameters.Parameters A × Y := (p₀.2, y₀.point)
  let c := BeltramiMarkedScaledSlices.chart π F hBranch s p₀
  let j := (BeltramiMarkedFiberMap.map π F hBranch p₀.2 y₀).point
  have hy : y₀ ∈ c.source := BeltramiMarkedFiberCharts.chart_center π F hBranch p₀.2 y₀.point
  have htarget : c y₀ ∈ c.target := c.map_source hy
  have hpower : y₀ ∈ BeltramiMarkedPowerPrimitives.domain π F hBranch j p₀ := by
    exact NativeBeltramiSurface.chart_center qX (BeltramiMarkedReferenceCharts.parameter A p₀.2)
      (BeltramiMarkedFiberMap.map π F hBranch p₀.2 y₀)
  have hstart : (p₀, c y₀) ∈ BeltramiMarkedUniformPrimitiveBounds.domain π F hBranch s j := by
    refine ⟨htarget, ?_⟩
    change BeltramiMarkedUniformSlices.inverse π F hBranch s (p₀, c y₀) ∈ BeltramiMarkedTotalPrimitives.domain π F hBranch j
    rw [BeltramiMarkedUniformSlices.inverse_value π F hBranch s p₀ htarget, c.left_inv hy]
    exact (BeltramiMarkedTotalPrimitives.domain_inclusion π F hBranch j p₀ y₀).mpr hpower
  have hopen : IsOpen ((fun z : ℂ => (p₀, z)) ⁻¹' BeltramiMarkedUniformPrimitiveBounds.domain π F hBranch s j) :=
    (BeltramiMarkedUniformPrimitiveBounds.domain_open π F hBranch s j).preimage (continuous_const.prodMk continuous_id)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hstart)
  refine ⟨j, ε / 2, by linarith, ?_⟩
  intro z hz
  apply hball
  change dist z (c y₀) < ε
  change dist z (c y₀) ≤ ε / 2 at hz
  exact lt_of_le_of_lt hz (by linarith)

end VeechDichotomy.BeltramiMarkedPrimitiveDisks
