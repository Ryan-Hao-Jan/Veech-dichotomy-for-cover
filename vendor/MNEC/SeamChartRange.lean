module

public import MNEC.HalfCollarRanges
public import MNEC.SeamOpenSets
public import MNEC.SeamChartMaps

@[expose] public section

/-!
# The range of a seam rectangle map is open

The explicit rectangle map covers the explicit saturated bank
neighborhood. This identifies its range in the independently constructed
quotient and proves that range open.
-/

noncomputable section

namespace MNEC.SeamChartRange

open LatticeTorus CutTorus SlitConnectedSum OffSlitEmbeddings SlitCollars
open CutBankLifts HalfCollarRanges SeamOpenSets SeamChartMaps Set

theorem chart_nonpositive {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (hq : q.val.2 ≤ 0) :
    chart C k q = negativeExtension C k q := by
  by_cases h : 0 ≤ q.val.2
  · have hz : q.val.2 = 0 := le_antisymm hq h
    rw [chart_positive C k q h]
    exact extensions_agree_zero C k q hz
  · exact chart_negative C k q (lt_of_not_ge h)

theorem positiveExtension_mem {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) :
    positiveExtension C k q ∈ seamNeighborhood C k := by
  refine ⟨Sum.inl (halfLift C.leftCollar k (leftAbsHalf C q)), ?_, rfl⟩
  rw [mem_rawNeighborhood_inl]
  exact halfLift_mem_bankNeighborhood C.leftCollar k (leftAbsHalf C q)

theorem negativeExtension_mem {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) :
    negativeExtension C k q ∈ seamNeighborhood C k := by
  refine ⟨Sum.inr (halfLift C.rightCollar (!k) (rightAbsHalf C q)), ?_, rfl⟩
  rw [mem_rawNeighborhood_inr]
  exact halfLift_mem_bankNeighborhood C.rightCollar (!k) (rightAbsHalf C q)

theorem range_chart {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) :
    range (chart C k) = seamNeighborhood C k := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, rfl⟩
    by_cases hq : 0 ≤ q.val.2
    · rw [chart_positive C k q hq]
      exact positiveExtension_mem C k q
    · rw [chart_negative C k q (lt_of_not_ge hq)]
      exact negativeExtension_mem C k q
  · rintro p ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · obtain ⟨u, hu⟩ := exists_halfLift_of_mem_bankNeighborhood C.leftCollar k x hx
      let q : Domain C := ⟨u.val, u.property.1⟩
      have habs : leftAbsHalf C q = u := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact abs_of_nonneg u.property.2
      refine ⟨q, ?_⟩
      rw [chart_positive C k q u.property.2]
      change left L₁ L₂ w (halfLift C.leftCollar k (leftAbsHalf C q)) = _
      rw [habs, hu]
      rfl
    · obtain ⟨u, hu⟩ := exists_halfLift_of_mem_bankNeighborhood C.rightCollar (!k) x hx
      have hu_upper : u.val.2 < C.r := u.property.1.2.2
      have hu_lower : -C.r < u.val.2 := u.property.1.2.1
      let q : Domain C := ⟨(u.val.1, -u.val.2),
        ⟨u.property.1.1, ⟨neg_lt_neg hu_upper, by linarith only [hu_lower]⟩⟩⟩
      have habs : rightAbsHalf C q = u := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change |-u.val.2| = u.val.2
          rw [abs_neg, abs_of_nonneg u.property.2]
      refine ⟨q, ?_⟩
      rw [chart_nonpositive C k q (neg_nonpos.mpr u.property.2)]
      change right L₁ L₂ w (halfLift C.rightCollar (!k) (rightAbsHalf C q)) = _
      rw [habs, hu]
      rfl

theorem range_chart_open {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : IsOpen (range (chart C k)) := by
  rw [range_chart]
  exact seamNeighborhood_open hw₁ hw₂ C k

end MNEC.SeamChartRange
