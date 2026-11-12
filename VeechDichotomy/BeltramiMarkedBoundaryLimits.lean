module

public import VeechDichotomy.ChartDiskBoundary
public import Mathlib.Topology.Sequences

/-! Nearby actual disk-frontier points and bounded target times have a
common subsequence with a REGULAR actual limit, whenever the limit disk
frontier is regular. Compact time-circle coordinates and joint inverse
continuity prove the result in the exact native limit fiber. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedBoundaryLimits

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)

theorem subsequence (s : ComplexBeltramiMarkParameters.Parameters A × Y) (p : ℕ → Base A) (p₀ : Base A)
    (hp : Tendsto p atTop (𝓝 p₀)) (z₀ : ℂ) {r : ℝ} (hr : 0 < r) (T : ℝ)
    (a : ℕ → ℝ) (y : ∀ n, BeltramiMarkedFiberSurface.Surface π F hBranch (p n).2)
    (ha : ∀ᶠ n in atTop, a n ∈ Icc 0 T)
    (hR₀ : Metric.closedBall z₀ r ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target)
    (hR : ∀ᶠ n in atTop, Metric.closedBall z₀ r ⊆ (BeltramiMarkedScaledSlices.chart π F hBranch s (p n)).target)
    (hfront : ∀ᶠ n in atTop, y n ∈ frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch s (p n) z₀ r))
    (hregular : ∀ z ∈ frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch s p₀ z₀ r),
      z ∈ regularSet (fiberForm π F hBranch p₀)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a₀ ∈ Icc 0 T, ∃ z : Regular (fiberForm π F hBranch p₀),
      Tendsto (a ∘ σ) atTop (𝓝 a₀) ∧
      Tendsto (fun n => inclusion π F hBranch (p (σ n)) (y (σ n))) atTop (𝓝 (inclusion π F hBranch p₀ z.val)) := by
  let c := fun n => BeltramiMarkedScaledSlices.chart π F hBranch s (p n)
  let f : ℕ → ℝ × ℂ := fun n => (a n, c n (y n))
  have hevent : ∀ᶠ n in atTop, f n ∈ Icc (0 : ℝ) T ×ˢ Metric.sphere z₀ r := by
    filter_upwards [ha, hR, hfront] with n hnA hnR hnF
    have hc := BeltramiMarkedRegularEscapeDisks.frontier_coordinates (c n) z₀ r hnR hnF
    exact ⟨hnA, hc.2⟩
  obtain ⟨w, hw, σ, hσ, hlim⟩ := (isCompact_Icc.prod (isCompact_sphere z₀ r)).tendsto_subseq' hevent.frequently
  have hwdist : dist w.2 z₀ = r := hw.2
  have hwtarget : w.2 ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).target := hR₀ hwdist.le
  let z := (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).symm w.2
  have hzfront : z ∈ frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch s p₀ z₀ r) :=
    ChartDiskBoundary.inverse_mem_frontier _ z₀ hr hR₀ hwdist
  have hzreg := hregular z hzfront
  have haLim : Tendsto (a ∘ σ) atTop (𝓝 w.1) := hlim.fst_nhds
  have hcLim : Tendsto (fun n => c (σ n) (y (σ n))) atTop (𝓝 w.2) := hlim.snd_nhds
  have hInv := BeltramiMarkedUniformSlices.inverse_tendsto π F hBranch s p₀ hwtarget
    ((hp.comp hσ.tendsto_atTop).prodMk_nhds hcLim)
  have heq : ∀ᶠ n in atTop,
      BeltramiMarkedUniformSlices.inverse π F hBranch s (p n, c n (y n)) = inclusion π F hBranch (p n) (y n) := by
    filter_upwards [hR, hfront] with n hnR hnF
    have hc := BeltramiMarkedRegularEscapeDisks.frontier_coordinates (c n) z₀ r hnR hnF
    rw [BeltramiMarkedUniformSlices.inverse_value π F hBranch s (p n) ((c n).map_source hc.1),
      (c n).left_inv hc.1]
  have hactual : Tendsto (fun n => inclusion π F hBranch (p (σ n)) (y (σ n))) atTop
      (𝓝 (BeltramiMarkedUniformSlices.inverse π F hBranch s (p₀, w.2))) :=
    Tendsto.congr' (hσ.tendsto_atTop.eventually heq) hInv
  rw [BeltramiMarkedUniformSlices.inverse_value π F hBranch s p₀ hwtarget] at hactual
  exact ⟨σ, hσ, w.1, hw.1, ⟨z, hzreg⟩, haLim, hactual⟩

end VeechDichotomy.BeltramiMarkedBoundaryLimits
