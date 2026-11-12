module

public import MNEC.FiniteConcentrationLimit
public import MNEC.NativeCompactDirectionalContinuation

/-! An actual native maximal directional trajectory tends to a genuine
zero at every finite excluded domain boundary. Compact regular continuation
proves concentration near the actual finite zero set; interval tails and
original compact Hausdorff topology derive a single limiting zero. No
endpoint escape or chosen-limit certificate is an input. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeTrajectoryZeroLimit

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeDirectionalDynamics
open Set Filter Topology
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem observed_continuousOn (q : Differential X) (v : Plane) (x : Regular q) :
    ContinuousOn (fun t : ℝ => (trajectory q v x t).val) (domain q v x) := by
  let := chartedSpace q
  exact continuous_subtype_val.comp_continuousOn (trajectory_isMIntegralCurveOn q v x).continuousOn

/-- Actual endpoint limit, for either finite side of the genuine native
maximal interval. The zero and the convergence are both derived. -/
theorem exists_zero_limit (q : Differential X) (v : Plane) (x : Regular q) (B : ℝ)
    (hB : B ∉ domain q v x) (hBoundary : B ∈ closure (domain q v x)) :
    ∃ z ∈ zeroSet q, Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[domain q v x] B) (𝓝 z) := by
  apply FiniteConcentrationLimit.exists_limit (domain q v x) (domain_convex q v x) B hBoundary
    (fun t : ℝ => (trajectory q v x t).val) (observed_continuousOn q v x) (zeroSet q) (zeroSet_finite q)
  intro U hU hzeros
  exact NativeCompactDirectionalContinuation.eventually_near_zeros q v x B hB U hU hzeros

end MNEC.NativeTrajectoryZeroLimit
