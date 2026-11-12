module

public import MNEC.CutBankLifts
public import MNEC.SeamClasses
public import Mathlib.Topology.Order.OrderClosed

/-!
# Continuous rectangle maps across the actual cross-glued seam

The two closed half-rectangles enter the two unrelated lattice tori.
Their common axis agrees by the specified opposite-bank quotient relation.
Continuity follows from closed-half pasting and the proved cut-bank lifts.
-/

noncomputable section
@[expose] public section

namespace MNEC.SeamChartMaps

open LatticeTorus CutTorus OffSlitEmbeddings SlitCollars CutBankLifts SlitConnectedSum
open Set Topology
open scoped Classical

abbrev Domain {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w) :=
  ↥(rectangle C.a C.b C.r)

def leftAbsHalf {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (q : Domain C) : HalfDomain C.leftCollar :=
  ⟨(q.val.1, |q.val.2|), by
    refine ⟨⟨q.property.1, ?_, ?_⟩, abs_nonneg _⟩
    · exact (neg_lt_zero.mpr C.r_pos).trans_le (abs_nonneg _)
    · exact abs_lt.mpr q.property.2⟩

def rightAbsHalf {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (q : Domain C) : HalfDomain C.rightCollar :=
  ⟨(q.val.1, |q.val.2|), by
    refine ⟨⟨q.property.1, ?_, ?_⟩, abs_nonneg _⟩
    · exact (neg_lt_zero.mpr C.r_pos).trans_le (abs_nonneg _)
    · exact abs_lt.mpr q.property.2⟩

theorem continuous_leftAbsHalf {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) : Continuous (leftAbsHalf C) :=
  (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.abs).subtype_mk _

theorem continuous_rightAbsHalf {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) : Continuous (rightAbsHalf C) :=
  (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.abs).subtype_mk _

def positiveExtension {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (k : Bool) (q : Domain C) : Surface L₁ L₂ w :=
  left L₁ L₂ w (halfLift C.leftCollar k (leftAbsHalf C q))

def negativeExtension {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (k : Bool) (q : Domain C) : Surface L₁ L₂ w :=
  right L₁ L₂ w (halfLift C.rightCollar (!k) (rightAbsHalf C q))

theorem continuous_positiveExtension {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (C : CommonCollar L₁ L₂ w) (k : Bool) :
    Continuous (positiveExtension C k) :=
  (continuous_left L₁ L₂ w).comp
    ((continuous_halfLift hw₁ C.leftCollar k).comp (continuous_leftAbsHalf C))

theorem continuous_negativeExtension {L₁ L₂ : Lattice} {w : Plane}
    (hw₂ : L₂.EmbeddedSlit w) (C : CommonCollar L₁ L₂ w) (k : Bool) :
    Continuous (negativeExtension C k) :=
  (continuous_right L₁ L₂ w).comp
    ((continuous_halfLift hw₂ C.rightCollar (!k)).comp (continuous_rightAbsHalf C))

theorem extensions_agree_zero {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (hq : q.val.2 = 0) :
    positiveExtension C k q = negativeExtension C k q := by
  have hzero₁ : (leftAbsHalf C q).val.2 = 0 := by
    change |q.val.2| = 0
    rw [hq, abs_zero]
  have hzero₂ : (rightAbsHalf C q).val.2 = 0 := by
    change |q.val.2| = 0
    rw [hq, abs_zero]
  unfold positiveExtension negativeExtension
  rw [halfLift_zero C.leftCollar k _ hzero₁, halfLift_zero C.rightCollar (!k) _ hzero₂]
  cases k with
  | false =>
    simpa only [Bool.not_false, interiorBank, upper, lower, leftAbsHalf, rightAbsHalf] using
      (upper_lower_glued L₁ L₂ w q.val.1
      (halfLongitudinal (leftAbsHalf C q)).1 (halfLongitudinal (leftAbsHalf C q)).2)
  | true =>
    simpa only [Bool.not_true, interiorBank, upper, lower, leftAbsHalf, rightAbsHalf] using
      (lower_upper_glued L₁ L₂ w q.val.1
      (halfLongitudinal (leftAbsHalf C q)).1 (halfLongitudinal (leftAbsHalf C q)).2)

def chart {L₁ L₂ : Lattice} {w : Plane} (C : CommonCollar L₁ L₂ w)
    (k : Bool) (q : Domain C) : Surface L₁ L₂ w :=
  if 0 ≤ q.val.2 then positiveExtension C k q else negativeExtension C k q

theorem chart_positive {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (hq : 0 ≤ q.val.2) :
    chart C k q = positiveExtension C k q := ite_eq_left hq

theorem chart_negative {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (hq : q.val.2 < 0) :
    chart C k q = negativeExtension C k q := ite_eq_right (not_le_of_gt hq)

theorem chart_zero {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (hq : q.val.2 = 0) :
    chart C k q = positiveExtension C k q := chart_positive C k q (hq ▸ le_rfl)

theorem continuous_chart {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : Continuous (chart C k) := by
  apply Continuous.if_le (continuous_positiveExtension hw₁ C k)
    (continuous_negativeExtension hw₂ C k) continuous_const continuous_subtype_val.snd
  intro q hq
  exact extensions_agree_zero C k q hq.symm

theorem positiveExtension_base {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (hq : 0 ≤ q.val.2) :
    base (halfLift C.leftCollar k (leftAbsHalf C q)) =
      L₁.project (frame w (q.val.1, sideSign k * q.val.2)) := by
  rw [base_halfLift]
  change L₁.project (frame w (q.val.1, sideSign k * |q.val.2|)) = _
  rw [abs_of_nonneg hq]

theorem negativeExtension_base {L₁ L₂ : Lattice} {w : Plane}
    (C : CommonCollar L₁ L₂ w) (k : Bool) (q : Domain C) (hq : q.val.2 ≤ 0) :
    base (halfLift C.rightCollar (!k) (rightAbsHalf C q)) =
      L₂.project (frame w (q.val.1, sideSign k * q.val.2)) := by
  rw [base_halfLift]
  change L₂.project (frame w (q.val.1, sideSign (!k) * |q.val.2|)) = _
  rw [abs_of_nonpos hq]
  cases k <;> simp [sideSign]

theorem chart_injective {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (C : CommonCollar L₁ L₂ w) (k : Bool) : Function.Injective (chart C k) := by
  intro p q heq
  by_cases hp : 0 ≤ p.val.2
  · by_cases hq : 0 ≤ q.val.2
    · rw [chart_positive C k p hp, chart_positive C k q hq] at heq
      have hcut := SeamClasses.left_injective L₁ L₂ w hw₁ hw₂ heq
      have hhalf := halfLift_injective C.leftCollar k hcut
      have hval := congrArg Subtype.val hhalf
      apply Subtype.ext
      apply Prod.ext
      · have hs := congrArg Prod.fst hval
        change p.val.1 = q.val.1 at hs
        exact hs
      · have hs := congrArg Prod.snd hval
        change |p.val.2| = |q.val.2| at hs
        simpa only [abs_of_nonneg hp, abs_of_nonneg hq] using hs
    · have hqn : q.val.2 < 0 := lt_of_not_ge hq
      rw [chart_positive C k p hp, chart_negative C k q hqn] at heq
      have hrel := (SeamClasses.left_eq_right_iff L₁ L₂ w hw₁ hw₂ _ _).1 heq
      have hoff : base (halfLift C.rightCollar (!k) (rightAbsHalf C q)) ∉ L₂.slitSet w := by
        rw [base_halfLift]
        exact halfBase_off_slit C.rightCollar (!k) (rightAbsHalf C q)
          (abs_ne_zero.mpr (ne_of_lt hqn))
      exact False.elim (hoff (SeamClasses.seam_target_on_slit hrel))
  · have hpn : p.val.2 < 0 := lt_of_not_ge hp
    by_cases hq : 0 ≤ q.val.2
    · rw [chart_negative C k p hpn, chart_positive C k q hq] at heq
      have hrel := (SeamClasses.left_eq_right_iff L₁ L₂ w hw₁ hw₂ _ _).1 heq.symm
      have hoff : base (halfLift C.rightCollar (!k) (rightAbsHalf C p)) ∉ L₂.slitSet w := by
        rw [base_halfLift]
        exact halfBase_off_slit C.rightCollar (!k) (rightAbsHalf C p)
          (abs_ne_zero.mpr (ne_of_lt hpn))
      exact False.elim (hoff (SeamClasses.seam_target_on_slit hrel))
    · have hqn : q.val.2 < 0 := lt_of_not_ge hq
      rw [chart_negative C k p hpn, chart_negative C k q hqn] at heq
      have hcut := SeamClasses.right_injective L₁ L₂ w hw₁ hw₂ heq
      have hhalf := halfLift_injective C.rightCollar (!k) hcut
      have hval := congrArg Subtype.val hhalf
      apply Subtype.ext
      apply Prod.ext
      · have hs := congrArg Prod.fst hval
        change p.val.1 = q.val.1 at hs
        exact hs
      · have hs := congrArg Prod.snd hval
        change |p.val.2| = |q.val.2| at hs
        simpa only [abs_of_neg hpn, abs_of_neg hqn, neg_inj] using hs

end MNEC.SeamChartMaps
