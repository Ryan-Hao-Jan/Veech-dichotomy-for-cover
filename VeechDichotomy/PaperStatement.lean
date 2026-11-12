module

public import VeechDichotomy.NativeAffineGroup
public import VeechDichotomy.NativeTranslationCover
public import VeechDichotomy.NativeDynamics

/-!
The requested theorem, stated with actual native mathematical objects.

`MainClaim` records the exact target proposition independently of its
proof. `VeechDichotomy.PaperMainTheorem.main` proves it from the actual
native lattice, cover and compact-configuration hypotheses.
-/

@[expose] public section

namespace VeechDichotomy.PaperStatement

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential
open NativeTranslationCover NativeAffineGroup NativeDynamics Set Topology
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

/-- A distinct ordered tuple enumerates precisely the actual branch values
and belongs to a compact invariant set in the distinct-configuration locus. -/
def HasCompactBranchConfigurations (π : Cover ωX ωY) : Prop :=
  ∃ (m : ℕ) (b : Fin m → X), Function.Injective b ∧ range b = branchValues π ∧
    ∃ F : Set (Fin m → X), IsCompact F ∧ invariant (AffineGroup ωX) F ∧
      b ∈ F ∧ F ⊆ configuration m X

/-- Unique ergodicity in every minimal direction, with invariant
probabilities on the actual complete nonsingular directional flow. -/
def StrictErgodicity (q : Differential Y) : Prop :=
  ∀ v : Plane, MinimalDirection q v → UniquelyErgodicDirection q v

/-- The main theorem of the supplied paper, proved in PaperMainTheorem. -/
def MainClaim (ωX : Differential X) (ωY : Differential Y) : Prop :=
  ∀ π : Cover ωX ωY, 2 ≤ genus X → NativeVeech.IsVeech ωX →
    HasCompactBranchConfigurations π → StrictErgodicity ωY

theorem compact_configuration_from_orbitClosure
    (π : Cover ωX ωY) {m : ℕ} {b : Fin m → X}
    (hb : range b = branchValues π)
    (hclosure : Disjoint (closure (MulAction.orbit (AffineGroup ωX) b))
      (fatDiagonal m X)) : HasCompactBranchConfigurations π := by
  obtain ⟨F, hF, hFi, hbF, hFc⟩ := (compact_configuration_iff ωX b).mpr hclosure
  exact ⟨m, b, hFc hbF, hb, F, hF, hFi, hbF, hFc⟩

theorem compact_configuration_of_subsingleton_tuple
    (π : Cover ωX ωY) {m : ℕ} [Subsingleton (Fin m)] {b : Fin m → X}
    (hb : range b = branchValues π) : HasCompactBranchConfigurations π := by
  obtain ⟨F, hF, hFi, hbF, hFc⟩ :=
    exists_compact_invariant_configuration_of_subsingleton (G := AffineGroup ωX) b
  exact ⟨m, b, Function.injective_of_subsingleton b, hb, F, hF, hFi, hbF, hFc⟩

end VeechDichotomy.PaperStatement
