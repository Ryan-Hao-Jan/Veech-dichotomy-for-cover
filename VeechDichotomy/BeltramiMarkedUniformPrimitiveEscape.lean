module

public import VeechDichotomy.BeltramiMarkedUniformPrimitiveBounds
public import VeechDichotomy.NativePrimitiveBoundedEscape

/-! Uniform bounded target-time escape on ACTUAL nearby native fibers.
A fixed closed source-coordinate disk in the actual power-primitive
domain supplies a common primitive bound, hence a common time by which
every complete vertical orbit starting inside reaches the disk frontier.
Zeros and ramification are allowed throughout the disk. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedUniformPrimitiveEscape

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeTranslationCover BeltramiPlane Set Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

def disk (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) (z₀ : ℂ) (r : ℝ) :
    Set (BeltramiMarkedFiberSurface.Surface π F hBranch p.2) :=
  (BeltramiMarkedScaledSlices.chart π F hBranch s p).source ∩
    (BeltramiMarkedScaledSlices.chart π F hBranch s p) ⁻¹' Metric.ball z₀ r

theorem disk_open (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : Base A) (z₀ : ℂ) (r : ℝ) :
    IsOpen (disk π F hBranch s p z₀ r) :=
  (BeltramiMarkedScaledSlices.chart π F hBranch s p).continuousOn.isOpen_inter_preimage
    (BeltramiMarkedScaledSlices.chart π F hBranch s p).open_source Metric.isOpen_ball

theorem uniform_escape (s : ComplexBeltramiMarkParameters.Parameters A × Y) (j : X) (p₀ : Base A) (z₀ : ℂ) (r : ℝ)
    (hsub : ∀ z ∈ Metric.closedBall z₀ r, (p₀, z) ∈ BeltramiMarkedUniformPrimitiveBounds.domain π F hBranch s j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ U : Set (Base A), IsOpen U ∧ p₀ ∈ U ∧ ∀ p ∈ U,
      ∀ x : CompleteOrbits (fiberForm π F hBranch p) vertical, x.val.val ∈ disk π F hBranch s p z₀ r →
        ∃ τ ∈ Icc 0 (2 * M + 1), (trajectory (fiberForm π F hBranch p) vertical x.val τ).val ∈
          frontier (disk π F hBranch s p z₀ r) := by
  obtain ⟨M, hM, U, hU, hpU, hbounds⟩ := BeltramiMarkedUniformPrimitiveBounds.uniform_bound π F hBranch s j p₀
    (isCompact_closedBall z₀ r) hsub
  refine ⟨M, hM, U, hU, hpU, ?_⟩
  intro p hp x hx
  have hdomain : ∀ y ∈ disk π F hBranch s p z₀ r, y ∈ BeltramiMarkedPowerPrimitives.domain π F hBranch j p := by
    intro y hy
    have hc := hbounds p hp _ (Metric.ball_subset_closedBall hy.2)
    simpa only [(BeltramiMarkedScaledSlices.chart π F hBranch s p).left_inv hy.1] using hc.2.1
  have hbound : ∀ y ∈ disk π F hBranch s p z₀ r, |(BeltramiMarkedPowerPrimitives.primitive π F hBranch j p y).im| ≤ M := by
    intro y hy
    have hc := hbounds p hp _ (Metric.ball_subset_closedBall hy.2)
    simpa only [(BeltramiMarkedScaledSlices.chart π F hBranch s p).left_inv hy.1] using hc.2.2
  exact NativePrimitiveBoundedEscape.reaches_frontier (fiberForm π F hBranch p) x _ (disk_open π F hBranch s p z₀ r)
    (BeltramiMarkedPowerPrimitives.primitive π F hBranch j p)
    (fun y hy => BeltramiMarkedPowerPrimitives.derivative π F hBranch j p y (hdomain y hy)) M hbound hx

end VeechDichotomy.BeltramiMarkedUniformPrimitiveEscape
