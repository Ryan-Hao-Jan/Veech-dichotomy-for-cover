module

public import VeechDichotomy.NativeDenseDirectionReturns
public import VeechDichotomy.PaperCompactReturnReduction

/-! The main theorem of the supplied paper for the actual native
translation surfaces and finite translation covers. All specified
direction returns follow from the actual native lattice condition;
no recurrence, cusp, compactness or ergodicity oracle is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PaperMainTheorem

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential NativeTranslationCover Set Topology
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

theorem main (ωX : Differential X) (ωY : Differential Y) : PaperStatement.MainClaim ωX ωY := by
  intro π hgenus hVeech hbranch
  apply PaperCompactReturnReduction.strict_ergodicity_of_dense_returns π hbranch
  intro v hv hdense
  obtain ⟨x, hx⟩ := hdense
  exact NativeDenseDirectionReturns.compact_returns ωX hgenus hVeech v hv x hx

theorem of_orbitClosure {ωX : Differential X} {ωY : Differential Y} (π : Cover ωX ωY)
    (hgenus : 2 ≤ genus X) (hVeech : NativeVeech.IsVeech ωX)
    {m : ℕ} {b : Fin m → X} (hb : range b = branchValues π)
    (hclosure : Disjoint (closure (MulAction.orbit (NativeAffineGroup.AffineGroup ωX) b))
      (fatDiagonal m X)) : PaperStatement.StrictErgodicity ωY :=
  main ωX ωY π hgenus hVeech (PaperStatement.compact_configuration_from_orbitClosure π hb hclosure)

end VeechDichotomy.PaperMainTheorem
