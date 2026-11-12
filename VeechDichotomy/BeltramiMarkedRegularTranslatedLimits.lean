module

public import VeechDichotomy.BeltramiMarkedPointCompactness
public import VeechDichotomy.BeltramiMarkedEscapeLimits

/-! EVERY original fixed complete source point has a regular translated
image limit along a strict subsequence of actual returning native fibers.
Properness first gives an arbitrary image limit; the actual uniform
primitive escape supplies bounded/convergent target-time translations.
No invariant-measure nonconcentration or positive area component is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRegularTranslatedLimits

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeCompleteDirectionalFlow NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup
open scoped Manifold ContDiff

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

theorem exists_regular_limit (p₀ : Base A) (hp : Tendsto p atTop (𝓝 p₀)) (x : CompleteOrbits q v) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ a : ℕ → ℝ, ∃ a₀ : ℝ,
      Tendsto a atTop (𝓝 a₀) ∧ ∃ y : Regular (fiberForm π F hBranch p₀),
        Tendsto (fun n => inclusion π F hBranch (p (σ n))
          (BeltramiMarkedShiftedSourcePoints.point π F hBranch q v hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) x a n).val)
          atTop (𝓝 (inclusion π F hBranch p₀ y.val)) := by
  obtain ⟨σ, hσ, y₀, hlim⟩ := BeltramiMarkedPointCompactness.subsequence π F hBranch q v hv t p e p₀ hp x.val
  have hlim' : Tendsto (fun n => inclusion π F hBranch (p (σ n))
      (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) x.val n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ y₀)) := by
    simp_rw [BeltramiMarkedNativePointValues.point_subsequence]
    exact hlim
  obtain ⟨τ, hτ, a, a₀, ha, y, hy⟩ := BeltramiMarkedEscapeLimits.regular_shifted_limit π F hBranch q v hv
    (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) p₀ (hp.comp hσ.tendsto_atTop) x y₀ hlim'
  refine ⟨σ ∘ τ, hσ.comp hτ, a, a₀, ha, y, ?_⟩
  simpa only [Function.comp_def] using hy

end VeechDichotomy.BeltramiMarkedRegularTranslatedLimits
