module

public import VeechDichotomy.BeltramiMarkedCompleteRayPoints
public import VeechDichotomy.BeltramiMarkedBoundaryLimits
public import VeechDichotomy.BeltramiMarkedNativePointValues

/-! A fixed complete source point whose original native images converge
to ANY actual limit point admits bounded target-time shifts with a regular
translated image limit. Actual uniform escape, complete phase transport
and compact time-circle extraction discharge every geometric input. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedEscapeLimits

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeTranslationCover BeltramiPlane Set Filter Topology NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : BeltramiPlane.Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (q : Differential Z) (v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv (t n)) (fiberForm π F hBranch (p n)))

theorem regular_shifted_limit (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (x : CompleteOrbits q v)
    (y₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n)
      (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x.val n).val) atTop (𝓝 (inclusion π F hBranch p₀ y₀))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → ℝ, ∃ a₀ : ℝ,
      Tendsto a atTop (𝓝 a₀) ∧ ∃ y : Regular (fiberForm π F hBranch p₀),
        Tendsto (fun n => inclusion π F hBranch (p (σ n))
          (BeltramiMarkedShiftedSourcePoints.point π F hBranch q v hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) x a n).val)
          atTop (𝓝 (inclusion π F hBranch p₀ y.val)) := by
  classical
  obtain ⟨r, hr, M, hM, U, hU, hpU, hregular, htarget, hescape⟩ :=
    BeltramiMarkedRegularEscapeDisks.uniform_regular_escape π F hBranch p₀ y₀
  let s : ComplexBeltramiMarkParameters.Parameters A × Y := (p₀.2, y₀.point)
  let z₀ := BeltramiMarkedScaledSlices.chart π F hBranch s p₀ y₀
  let c := fun n => BeltramiMarkedScaledSlices.chart π F hBranch s (p n)
  let phase := BeltramiMarkedCompleteRayPoints.phase π F hBranch q v hv t p e x
  have hyS : inclusion π F hBranch p₀ y₀ ∈ BeltramiMarkedSliceCoordinates.source π F hBranch s :=
    BeltramiMarkedLimitFlatCharts.center π F hBranch p₀ y₀
  have hsource := BeltramiMarkedSliceCoordinates.eventually_source π F hBranch s hyS hx
  have hcoordinate := BeltramiMarkedSliceCoordinates.coordinate_tendsto π F hBranch s hyS hx
  have hcomplex := toPlane.symm.continuous.continuousAt.tendsto.comp hcoordinate
  have hcomplex' : Tendsto (fun n => c n (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x.val n).val)
      atTop (𝓝 z₀) := by
    simpa only [Function.comp_def, BeltramiMarkedSliceCoordinates.coordinate_inclusion, toPlane.symm_apply_apply] using hcomplex
  have hinside : ∀ᶠ n in atTop, (phase n).val.val ∈ BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch s (p n) z₀ r := by
    filter_upwards [hsource, hcomplex' (Metric.ball_mem_nhds z₀ hr)] with n hnS hnB
    change (BeltramiMarkedCompleteRayPoints.phase π F hBranch q v hv t p e x n).val.val ∈
      BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch s (p n) z₀ r
    rw [BeltramiMarkedCompleteRayPoints.phase_value]
    exact ⟨hnS, hnB⟩
  have hpUevent : ∀ᶠ n in atTop, p n ∈ U := hp (hU.mem_nhds hpU)
  let Good := fun n τ => τ ∈ Icc 0 (2 * M + 1) ∧
    (trajectory (fiberForm π F hBranch (p n)) vertical (phase n).val τ).val ∈
      frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch s (p n) z₀ r)
  have hgood : ∀ᶠ n in atTop, ∃ τ, Good n τ := by
    filter_upwards [hpUevent, hinside] with n hnP hnI
    exact hescape (p n) hnP (phase n) hnI
  have hselect : ∀ n, ∃ τ, τ ∈ Icc 0 (2 * M + 1) ∧ ((∃ a, Good n a) → Good n τ) := by
    intro n
    by_cases h : ∃ a, Good n a
    · obtain ⟨a, ha⟩ := h
      exact ⟨a, ha.1, fun _ => ha⟩
    · exact ⟨0, ⟨le_rfl, by linarith⟩, fun hn => False.elim (h hn)⟩
  choose a ha hachoice using hselect
  let y := fun n => (trajectory (fiberForm π F hBranch (p n)) vertical (phase n).val (a n)).val
  have hyfront : ∀ᶠ n in atTop, y n ∈ frontier (BeltramiMarkedUniformPrimitiveEscape.disk π F hBranch s (p n) z₀ r) :=
    hgood.mono (fun n hn => (hachoice n hn).2)
  obtain ⟨σ, hσ, a₀, _, z, haLim, hzLim⟩ := BeltramiMarkedBoundaryLimits.subsequence π F hBranch s p p₀ hp z₀ hr (2 * M + 1)
    a y (Eventually.of_forall ha) (htarget p₀ hpU) (hpUevent.mono (fun n hn => htarget (p n) hn)) hyfront hregular
  refine ⟨σ, hσ, a ∘ σ, a₀, haLim, z, ?_⟩
  have heq (n : ℕ) :
      (BeltramiMarkedShiftedSourcePoints.point π F hBranch q v hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) x (a ∘ σ) n).val = y (σ n) := by
    rw [BeltramiMarkedNativePointValues.shifted_point_subsequence,
      BeltramiMarkedCompleteRayPoints.shifted_point_flow_value]
    rfl
  simpa only [heq] using hzLim

end VeechDichotomy.BeltramiMarkedEscapeLimits
