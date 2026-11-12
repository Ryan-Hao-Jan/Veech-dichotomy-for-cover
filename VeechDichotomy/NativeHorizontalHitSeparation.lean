module

public import VeechDichotomy.NativeHorizontalSides
public import VeechDichotomy.SeparatedWindowCounts

/-! Distinct hits of one vertical side by the actual native horizontal
trajectory are separated by more than the width of the rectangle. A
shorter return would still lie on the proved straight chart segment,
where its horizontal coordinate has strictly increased. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeHorizontalHitSeparation

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles NativeHorizontalSides
open Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

theorem ordered_gap {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) {s t : ℝ}
    (hs : s ∈ hitTimes q i x c b u) (ht : t ∈ hitTimes q i x c b u) (hst : s < t) :
    d - c < t - s := by
  by_contra hgap
  have hle : t - s ≤ d - c := le_of_not_gt hgap
  have hnew : c + (t - s) ∈ Ioo l r := by
    constructor <;> linarith [hc.1, hd.2]
  have hstep := side_transport q i hc hnew hR hs.2
  have heq : c + (t - s) - c = t - s := by ring
  rw [heq] at hstep
  have hflow := trajectory_add q horizontal x s hs.1 (t - s) hstep.1
  have hnewSide : trajectory q horizontal x t ∈ side q i (c + (t - s)) b u := by
    simpa only [hflow, sub_add_cancel] using hstep.2
  have hfirst := hnewSide.2.1
  have hold := ht.2.2.1
  linarith

theorem separated {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) :
    SeparatedWindowCounts.Separated (d - c) (hitTimes q i x c b u) := by
  intro s hs t ht hst
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have hgap := ordered_gap q i hc hd hR x hs ht hlt
    rw [abs_of_neg (sub_neg.mpr hlt)]
    linarith
  · have hgap := ordered_gap q i hc hd hR x ht hs hgt
    rw [abs_of_pos (sub_pos.mpr hgt)]
    exact hgap

theorem finite_hits {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r) (hcd : c < d)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) (a z : ℝ) :
    (hitTimes q i x c b u ∩ Icc a z).Finite :=
  SeparatedWindowCounts.finite_window (sub_pos.mpr hcd) (separated q i hc hd hR x) a z

theorem count_bounds {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r) (hcd : c < d)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) (a z : ℝ) :
    SeparatedWindowCounts.count (hitTimes q i x c b u) a z ≤
        SeparatedWindowCounts.count (hitTimes q i x d b u) a z + 1 ∧
      SeparatedWindowCounts.count (hitTimes q i x d b u) a z ≤
        SeparatedWindowCounts.count (hitTimes q i x c b u) a z + 1 :=
  SeparatedWindowCounts.translate_count_bounds (sub_pos.mpr hcd) (separated q i hc hd hR x)
    (hit_shift_iff q i hc hd hR x) a z

end VeechDichotomy.NativeHorizontalHitSeparation
