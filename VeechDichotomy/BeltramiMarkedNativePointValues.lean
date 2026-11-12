module

public import VeechDichotomy.BeltramiMarkedSL2SourceMaps
public import VeechDichotomy.BeltramiMarkedShiftedSourcePoints

/-! The regular native ray point map and the area-preserving original
surface comparison map are literally the same underlying map. Exact
zero-shift and subsequence formulas connect conull point selection to
the already proved native statistical comparisons. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedNativePointValues

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeTranslationCover BeltramiPlane Set
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

theorem point_value (x : Regular q) (n : ℕ) :
    (BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x n).val =
      BeltramiMarkedSL2SourceMaps.homeomorph π F hBranch q (fun n => NativeTeichmullerRay.matrix v hv (t n)) p e n x.val := rfl

theorem point_zero_shift (x : CompleteOrbits q v) (n : ℕ) :
    BeltramiMarkedShiftedSourcePoints.point π F hBranch q v hv t p e x (fun _ => 0) n =
      BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x.val n := by
  rw [BeltramiMarkedShiftedSourcePoints.point_eq_target_trajectory, trajectory_initial]

theorem point_subsequence (σ : ℕ → ℕ) (x : Regular q) (n : ℕ) :
    BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) x n =
      BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x (σ n) := rfl

theorem shifted_point_subsequence (σ : ℕ → ℕ) (x : CompleteOrbits q v) (a : ℕ → ℝ) (n : ℕ) :
    BeltramiMarkedShiftedSourcePoints.point π F hBranch q v hv (t ∘ σ) (p ∘ σ) (fun k => e (σ k)) x (a ∘ σ) n =
      BeltramiMarkedShiftedSourcePoints.point π F hBranch q v hv t p e x a (σ n) := rfl

end VeechDichotomy.BeltramiMarkedNativePointValues
