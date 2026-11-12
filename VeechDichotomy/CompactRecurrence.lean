module

public import VeechDichotomy.MarkedOrbit
public import VeechDichotomy.CompactTransport
public import Mathlib.Order.Filter.AtTopBot.CompleteLattice

/-! Nondivergence through an actual marked-deformation quotient and a
proper cover projection. No unique-ergodicity criterion is assumed.
-/

@[expose] public section

open Set Topology Filter

namespace VeechDichotomy

/-- Arbitrarily late returns to some fixed compact set. -/
def HasCompactReturns {X : Type*} [TopologicalSpace X] (u : ℝ → X) : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∃ᶠ t in atTop, u t ∈ K

theorem HasCompactReturns.map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {u : ℝ → X} (hu : HasCompactReturns u) {f : X → Y} (hf : Continuous f) :
    HasCompactReturns (f ∘ u) := by
  obtain ⟨K, hK, huK⟩ := hu
  exact ⟨f '' K, hK.image hf, huK.mono (fun t ht => mem_image_of_mem f ht)⟩

theorem HasCompactReturns.of_proper_projection
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {u : ℝ → X} {P : X → Y} (hP : IsProperMap P)
    (hu : HasCompactReturns (P ∘ u)) : HasCompactReturns u := by
  obtain ⟨K, hK, huK⟩ := hu
  exact ⟨P ⁻¹' K, hP.isCompact_preimage hK, huK⟩

theorem HasCompactReturns.not_divergent
    {X : Type*} [TopologicalSpace X] {u : ℝ → X} (hu : HasCompactReturns u) :
    ¬ Tendsto u atTop (cocompact X) := by
  obtain ⟨K, hK, huK⟩ := hu
  intro hdiv
  exact huK (hdiv hK.compl_mem_cocompact)

/-- Recurrence in G/range(D) lifts to recurrence of the marked
deformation when the original marking stays in a compact invariant set. -/
theorem HasCompactReturns.marked
    {G H Z : Type*} [Group G] [Group H] [MulAction H Z]
    [TopologicalSpace G] [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    [TopologicalSpace Z] (D : H →* G)
    {F : Set Z} (hF : IsCompact F) (hFi : invariant H F) {b : Z} (hb : b ∈ F)
    {a : ℝ → G}
    (ha : HasCompactReturns (fun t => (QuotientGroup.mk (a t) : G ⧸ D.range))) :
    HasCompactReturns (fun t => markedClass D (a t, b)) := by
  obtain ⟨C, hC, haC⟩ := ha
  obtain ⟨B, hB, hCB⟩ := compact_marked_returns D hF hFi hb hC
  exact ⟨B, hB, haC.mono (fun t ht => hCB (a t) ht)⟩

end VeechDichotomy
