module

public import VeechDichotomy.NativeAffineGroup
public import VeechDichotomy.ConfigurationSpace
public import VeechDichotomy.CompactRecurrence

/-! Native specialization of the compact marked-return argument.
The quotient in the conclusion consists of DISTINCT marked tuples on an
actual compact translation surface. Base recurrence remains a hypothesis;
the Veech recurrence theorem is not asserted or postulated here.
-/

@[expose] public section

namespace VeechDichotomy.NativeMarkedReturns

open MNEC.NativeAbelianDifferential NativeAffineGroup LinearGroup Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

abbrev NativeMarkedSpace (q : Differential X) (m : ℕ) :=
  MarkedOrbit (derivative q) (ConfigurationSpace m X)

theorem compact_returns_from_base_returns (q : Differential X) {m : ℕ}
    {F : Set (Fin m → X)} (hF : IsCompact F) (hFi : invariant (AffineGroup q) F)
    (hFc : F ⊆ configuration m X) {b : Fin m → X} (hb : b ∈ F)
    {a : ℝ → SL2}
    (ha : HasCompactReturns
      (fun t => (QuotientGroup.mk (a t) : SL2 ⧸ (derivative q).range))) :
    HasCompactReturns (fun t =>
      markedClass (derivative q) (a t, (⟨b, hFc hb⟩ : ConfigurationSpace m X))) := by
  exact ha.marked (derivative q) (isCompact_configurationSpace_lift hF hFc)
    (invariant_configurationSpace_lift hFi) hb

end VeechDichotomy.NativeMarkedReturns
