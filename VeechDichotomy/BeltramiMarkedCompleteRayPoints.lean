module

public import VeechDichotomy.NativeSL2CompletePhaseTransport
public import VeechDichotomy.BeltramiMarkedShiftedSourcePoints

/-! Actual complete target vertical phases along the returning native
ray. Their underlying points are precisely the already constructed ray
point images; target flow shifts are the actual shifted source images. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedCompleteRayPoints

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeTranslationCover BeltramiPlane NativePrimitiveRectangles
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences
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
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : Set.range b = branchValues π)
variable (q : Differential Z) (v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (p : ℕ → Base A)

local instance (B : SL2) : ChartedSpace ℂ (WholeSurface q B) := WholeDeformedAtlas.chartedSpace q B
local instance (B : SL2) : IsManifold 𝓘(ℂ) ω (WholeSurface q B) := WholeDeformedAtlas.isComplexManifold q B ω

variable (e : ∀ n, MNEC.NativeDifferentialEquiv.Equiv (NativeTeichmullerRay.rayForm q v hv (t n)) (fiberForm π F hBranch (p n)))

theorem velocity (n : ℕ) : planeEquiv (NativeTeichmullerRay.matrix v hv (t n)) v =
    NativeTeichmullerRay.contraction v (t n) • vertical := by
  simpa only [NativeTeichmullerRay.vertical, vertical] using NativeTeichmullerRay.contracted_velocity v hv (t n)

def phase (x : CompleteOrbits q v) (n : ℕ) : CompleteOrbits (fiberForm π F hBranch (p n)) vertical :=
  NativeSL2CompletePhaseTransport.toTarget q (NativeTeichmullerRay.matrix v hv (t n)) (fiberForm π F hBranch (p n))
    (e n) (NativeTeichmullerRay.contraction_pos v hv (t n)).ne' (velocity v hv t n) x

theorem phase_value (x : CompleteOrbits q v) (n : ℕ) : (phase π F hBranch q v hv t p e x n).val =
    BeltramiMarkedRayOrbitCounts.point π F hBranch q v hv t p e x.val n := rfl

theorem shifted_point_flow_value (x : CompleteOrbits q v) (a : ℕ → ℝ) (n : ℕ) :
    BeltramiMarkedShiftedSourcePoints.point π F hBranch q v hv t p e x a n =
      (timeMap (fiberForm π F hBranch (p n)) vertical (a n) (phase π F hBranch q v hv t p e x n)).val := by
  rw [BeltramiMarkedShiftedSourcePoints.point_eq_target_trajectory]
  rfl

end VeechDichotomy.BeltramiMarkedCompleteRayPoints
