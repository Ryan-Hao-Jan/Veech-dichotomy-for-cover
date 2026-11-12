module

public import VeechDichotomy.NativeSL2ArcTransport
public import MNEC.NativeCompleteDirectionalFlow

/-! Actual SL2/native equivalences carry complete native trajectories
to complete native trajectories, with the computed nonzero velocity
clock. Completeness is derived from the proved maximal-domain formula. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeSL2CompletePhaseTransport

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeDeformationRegular WholeDeformedAtlas LinearGroup LinearEquivalences Set
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (q : Differential X) (A : SL2) (r : Differential Y)

local instance : ChartedSpace ℂ (WholeSurface q A) := WholeDeformedAtlas.chartedSpace q A
local instance : IsManifold 𝓘(ℂ) ω (WholeSurface q A) := WholeDeformedAtlas.isComplexManifold q A ω

variable (e : MNEC.NativeDifferentialEquiv.Equiv (transformed q A) r)

theorem target_complete {v u : Plane} {k : ℝ} (hk : k ≠ 0) (hvel : planeEquiv A v = k • u)
    (x : CompleteOrbits q v) :
    domain r u (NativeSL2ArcTransport.homeomorph q A r e x.val) = univ := by
  apply eq_univ_of_forall
  intro t
  have ht := complete_time_mem q v x (t / k)
  rw [NativeSL2ArcTransport.domain_clock q A r e hk hvel x.val] at ht
  simpa only [mem_ofPred_eq, div_mul_cancel₀ _ hk] using ht

def toTarget {v u : Plane} {k : ℝ} (hk : k ≠ 0) (hvel : planeEquiv A v = k • u)
    (x : CompleteOrbits q v) : CompleteOrbits r u :=
  ⟨NativeSL2ArcTransport.homeomorph q A r e x.val, target_complete q A r e hk hvel x⟩

theorem value {v u : Plane} {k : ℝ} (hk : k ≠ 0) (hvel : planeEquiv A v = k • u)
    (x : CompleteOrbits q v) : (toTarget q A r e hk hvel x).val = NativeSL2ArcTransport.homeomorph q A r e x.val := rfl

theorem flow_clock {v u : Plane} {k : ℝ} (hk : k ≠ 0) (hvel : planeEquiv A v = k • u)
    (x : CompleteOrbits q v) (t : ℝ) :
    toTarget q A r e hk hvel (timeMap q v t x) = timeMap r u (t * k) (toTarget q A r e hk hvel x) := by
  apply Subtype.ext
  exact NativeSL2ArcTransport.trajectory_clock q A r e hk hvel x.val t (complete_time_mem q v x t)

end VeechDichotomy.NativeSL2CompletePhaseTransport
