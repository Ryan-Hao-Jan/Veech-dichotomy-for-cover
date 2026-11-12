module

public import VeechDichotomy.NativeCoverReturnErgodicity
public import VeechDichotomy.NativeCoverFlow
public import VeechDichotomy.PaperStatement

/-! The exact paper conclusion follows once specified dense base
directions have actual compact quotient returns. Minimal cover orbits
project to genuine dense complete base orbits, and the proved concrete
cover-return ergodicity theorem supplies every source direction.
NativeDenseDirectionReturns proves this return condition from the native
lattice hypothesis; PaperMainTheorem applies this reduction. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PaperCompactReturnReduction

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeCompleteDirectionalFlow
open NativeTranslationCover NativeVeech LinearGroup Set Topology
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y}

theorem strict_ergodicity_of_dense_returns (π : Cover qX qY) (hbranch : PaperStatement.HasCompactBranchConfigurations π)
    (hreturns : ∀ (v : Plane) (hv : v ≠ 0),
      (∃ x : CompleteOrbits qX v, DenseRange (fun t : ℝ => (flow qX v t x).val.val)) →
      HasCompactReturns (fun t => (QuotientGroup.mk (NativeTeichmullerRay.matrix v hv t) : SL2 ⧸ derivativeGroup qX))) :
    PaperStatement.StrictErgodicity qY := by
  obtain ⟨m, b, _, hb, C, hC, hCi, hbC, hconf⟩ := hbranch
  intro v hmin
  exact NativeCoverReturnErgodicity.uniquely_ergodic π b hb hC hCi hbC hconf v hmin.1 hmin
    (hreturns v hmin.1 (NativeCoverFlow.exists_dense_base_orbit_of_minimal_cover π v hmin))

end VeechDichotomy.PaperCompactReturnReduction
