module

public import VeechDichotomy.NativeLatticePointwiseCusp
public import VeechDichotomy.NativeParabolicDirectionObstruction
public import VeechDichotomy.CompactReturnNondivergence

/-! Every actual nonzero direction with an actual dense complete orbit
on a native genus-at-least-two Veech surface has actual compact quotient
returns. The proved pointwise cusp theorem and the proved native affine
parabolic obstruction exclude divergence for the specified direction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeDenseDirectionReturns

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeCompleteDirectionalFlow
open NativeVeech NativeTeichmullerRay LinearGroup Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem compact_returns (q : Differential X) (hgenus : 2 ≤ genus X) (hVeech : IsVeech q)
    (v : Plane) (hv : v ≠ 0) (x : CompleteOrbits q v)
    (hdense : DenseRange (fun t : ℝ => (flow q v t x).val.val)) :
    HasCompactReturns (fun t => (QuotientGroup.mk (matrix v hv t) : SL2 ⧸ derivativeGroup q)) := by
  apply (hasCompactReturns_iff_not_divergent _).mpr
  intro hescape
  obtain ⟨s, hs, hmem⟩ := NativeLatticePointwiseCusp.escaping_has_lower (derivativeGroup q) hVeech
    (rotationToVertical v hv) hescape
  exact NativeParabolicDirectionObstruction.rotated_shear_not_mem q hgenus v hv x hdense hs hmem

end VeechDichotomy.NativeDenseDirectionReturns
