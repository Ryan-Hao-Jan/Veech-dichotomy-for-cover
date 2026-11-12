module

public import VeechDichotomy.BeltramiMarkedRayOrbitCounts
public import VeechDichotomy.NativeRayReferenceTimes

/-! Actual shifted source clocks along a returning native ray. Their
ratios to the inverse contraction converge to the actual target chart
height differences. Every common positive target interval gives exactly
equal divergent source lengths, regardless of vertex heights. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedShiftedClocks

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Filter Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedSliceCoordinates NativeDeformationRegular WholeDeformedAtlas LinearGroup
open BeltramiMarkedRayOrbitCounts
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

def time (s : ComplexBeltramiMarkParameters.Parameters A × Y) (x : Regular q) (a : ℝ) (n : ℕ) : ℝ :=
  (a - (coordinate π F hBranch s
    (inclusion π F hBranch (p n) (point π F hBranch q v hv t p e x n).val)).2) /
      NativeTeichmullerRay.contraction v (t n)

def length (lo hi : ℝ) (n : ℕ) : ℝ := (hi - lo) / NativeTeichmullerRay.contraction v (t n)

theorem interval_length (s : ComplexBeltramiMarkParameters.Parameters A × Y) (x : Regular q) (lo hi : ℝ) (n : ℕ) :
    time π F hBranch q v hv t p e s x hi n - time π F hBranch q v hv t p e s x lo n =
      length v t lo hi n := by
  unfold time length
  ring

include hv in
theorem length_tendsto (ht : Tendsto t atTop atTop) {lo hi : ℝ} (hlohi : lo < hi) :
    Tendsto (length v t lo hi) atTop atTop := by
  exact NativeRayRectangleComparison.lifted_time_tendsto v hv ht tendsto_const_nhds (sub_pos.mpr hlohi)

theorem time_ratio_tendsto (s : ComplexBeltramiMarkParameters.Parameters A × Y)
    (p₀ : Base A) (x₀ : BeltramiMarkedFiberSurface.Surface π F hBranch p₀.2)
    (hx₀ : x₀ ∈ (BeltramiMarkedScaledSlices.chart π F hBranch s p₀).source)
    (x : Regular q) (a : ℝ)
    (hx : Tendsto (fun n => inclusion π F hBranch (p n) (point π F hBranch q v hv t p e x n).val)
      atTop (𝓝 (inclusion π F hBranch p₀ x₀))) :
    Tendsto (fun n => time π F hBranch q v hv t p e s x a n / NativeRayReferenceTimes.reference v (t n))
      atTop (𝓝 (a - (coordinate π F hBranch s (inclusion π F hBranch p₀ x₀)).2)) := by
  have hcoord := BeltramiMarkedSliceCoordinates.coordinate_tendsto π F hBranch s hx₀ hx
  exact NativeRayReferenceTimes.lifted_ratio_tendsto v hv t _ (tendsto_const_nhds.sub hcoord.snd_nhds)

end VeechDichotomy.BeltramiMarkedShiftedClocks
