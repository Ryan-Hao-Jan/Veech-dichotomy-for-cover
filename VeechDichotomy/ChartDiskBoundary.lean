module

public import VeechDichotomy.BeltramiMarkedRegularEscapeDisks
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Coordinate circles inside genuine chart targets parametrize the
entire actual chart-disk frontier. This supplies the reverse inclusion
needed when nearby escape points converge in fixed coordinates. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.ChartDiskBoundary

open Set Topology BeltramiMarkedRegularEscapeDisks

variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]

omit [T2Space Ω] in
theorem inverse_mem_frontier (c : OpenPartialHomeomorph Ω ℂ) (z₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hR : Metric.closedBall z₀ r ⊆ c.target) {z : ℂ} (hz : dist z z₀ = r) :
    c.symm z ∈ frontier (chartDisk c z₀ r) := by
  have hztarget : z ∈ c.target := hR (hz.le)
  have hzclosure : z ∈ closure (Metric.ball z₀ r) := by
    rw [closure_ball z₀ hr.ne']
    exact hz.le
  have hcl := mem_closure_image (c.symm.continuousAt hztarget) hzclosure
  have hsub : c.symm '' Metric.ball z₀ r ⊆ chartDisk c z₀ r := by
    rintro y ⟨w, hw, rfl⟩
    have hwt := hR (Metric.ball_subset_closedBall hw)
    exact ⟨c.map_target hwt, by simpa only [mem_preimage, c.right_inv hwt] using hw⟩
  refine ⟨closure_mono hsub hcl, ?_⟩
  have hU : IsOpen (chartDisk c z₀ r) := chartDisk_open c z₀ r
  rw [hU.interior_eq]
  intro hy
  have hdist : dist (c (c.symm z)) z₀ < r := hy.2
  rw [c.right_inv hztarget, hz] at hdist
  exact (lt_irrefl r) hdist

theorem frontier_iff (c : OpenPartialHomeomorph Ω ℂ) (z₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (hR : Metric.closedBall z₀ r ⊆ c.target) (y : Ω) :
    y ∈ frontier (chartDisk c z₀ r) ↔ y ∈ c.source ∧ dist (c y) z₀ = r := by
  refine ⟨frontier_coordinates c z₀ r hR, ?_⟩
  rintro ⟨hy, hdist⟩
  have hmem := inverse_mem_frontier c z₀ hr hR hdist
  simpa only [c.left_inv hy] using hmem

end VeechDichotomy.ChartDiskBoundary
