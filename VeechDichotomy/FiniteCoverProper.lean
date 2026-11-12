module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocalAtTarget

/-! Finite covering maps are proper, proved from local trivializations.
The paper uses an orbifold covering of moduli spaces, so applying this
lemma there still requires construction and control of orbifold charts.
-/

@[expose] public section

open Set Topology TopologicalSpace

namespace VeechDichotomy

theorem isProperMap_of_finite_covering
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
    (hf : IsCoveringMap f) (hfinite : ∀ x : X, (f ⁻¹' {x}).Finite) :
    IsProperMap f := by
  classical
  choose U hxU hU hfU H hH using fun x : X => (hf x).2
  have hcover : IsOpenCover (fun x : X => (⟨U x, hU x⟩ : Opens X)) := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨x, hxU x⟩
  have hclosed : IsClosedMap f := by
    rw [hcover.isClosedMap_iff_restrictPreimage]
    intro x
    let : Finite (f ⁻¹' {x}) := (hfinite x).to_subtype
    have heq : (U x).restrictPreimage f = Prod.fst ∘ H x := by
      funext z
      apply Subtype.ext
      exact (hH x z).symm
    rw [heq]
    exact isClosedMap_fst_of_compactSpace.comp (H x).isClosedMap
  exact isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨hf.continuous, hclosed, fun x => (hfinite x).isCompact⟩

end VeechDichotomy
