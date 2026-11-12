module

public import VeechDichotomy.CompactRecurrence

/-! Arbitrarily late returns to one actual compact set are equivalent
to failure of divergence through the actual cocompact filter. This
equivalence assumes no moduli topology or directional recurrence theorem. -/

@[expose] public section

namespace VeechDichotomy

open Set Filter Topology

theorem hasCompactReturns_iff_not_divergent {X : Type*} [TopologicalSpace X] (u : ℝ → X) :
    HasCompactReturns u ↔ ¬ Tendsto u atTop (cocompact X) := by
  classical
  constructor
  · exact HasCompactReturns.not_divergent
  · intro hdiv
    by_contra hreturns
    apply hdiv
    apply hasBasis_cocompact.tendsto_right_iff.mpr
    intro K hK
    exact not_frequently.mp (fun hfreq => hreturns ⟨K, hK, hfreq⟩)

end VeechDichotomy
