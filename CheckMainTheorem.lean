module

import VeechDichotomy
import Lean

open Lean Elab Command

/-! Independent replay gates for the exact target proposition and the
literal compact-branch-configuration statement of Theorem 1. -/

noncomputable section

namespace VeechDichotomy.MainTheoremVerification

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential NativeTranslationCover NativeDynamics Set Topology
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

example (ωX : Differential X) (ωY : Differential Y) : PaperStatement.MainClaim ωX ωY :=
  PaperMainTheorem.main ωX ωY

example (ωX : Differential X) (ωY : Differential Y) (π : Cover ωX ωY)
    (hgenus : 2 ≤ genus X) (hVeech : NativeVeech.IsVeech ωX)
    (m : ℕ) (b : Fin m → X) (hdistinct : Function.Injective b) (hbranch : range b = branchValues π)
    (F : Set (Fin m → X)) (hcompact : IsCompact F)
    (hinvariant : invariant (NativeAffineGroup.AffineGroup ωX) F) (hbF : b ∈ F) (hconf : F ⊆ configuration m X) :
    ∀ v : Plane, MinimalDirection ωY v → UniquelyErgodicDirection ωY v :=
  PaperMainTheorem.main ωX ωY π hgenus hVeech ⟨m, b, hdistinct, hbranch, F, hcompact, hinvariant, hbF, hconf⟩

end VeechDichotomy.MainTheoremVerification

#check @VeechDichotomy.PaperMainTheorem.main
#print axioms VeechDichotomy.PaperMainTheorem.main
#print axioms VeechDichotomy.NativeLatticePointwiseCusp.escaping_has_lower

run_cmd logInfo "MAIN_THEOREM_CHECK_PASSED: VeechDichotomy.PaperMainTheorem.main proves the exact MainClaim and literal Theorem 1."
