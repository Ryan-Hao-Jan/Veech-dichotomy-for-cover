module

public import VeechDichotomy.NativePrimitiveRectangles
public import VeechDichotomy.SeparatedWindowCounts

/-! Open native vertical flowboxes and their actual base-hit sets.
Buffered primitive rectangles give straight coordinates for every
short visit, and force distinct base hits to be strictly separated. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeVerticalFlowboxes

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativePrimitiveRectangles Set Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

def base (l r b : ℝ) : Set (Regular q) :=
  {y | y ∈ (chart q i).source ∧ (chart q i y).1 ∈ Ioo l r ∧ (chart q i y).2 = b}

def box (l r b h : ℝ) : Set (Regular q) :=
  (chart q i).source ∩ (chart q i) ⁻¹' rectangle l r b (b + h)

def hitTimes (x : CompleteOrbits q vertical) (l r b : ℝ) : Set ℝ :=
  {s | (timeMap q vertical s x).val ∈ base q i l r b}

theorem box_open (l r b h : ℝ) : IsOpen (box q i l r b h) :=
  (chart q i).continuousOn.isOpen_inter_preimage (chart q i).open_source
    (isOpen_Ioo.prod isOpen_Ioo)

theorem coordinates {l r b u : ℝ} (hR : rectangle l r b u ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) (hx : x.val ∈ (chart q i).source)
    (hxr : chart q i x.val ∈ rectangle l r b u) {t : ℝ}
    (ht : t ∈ Ioo (b - (chart q i x.val).2) (u - (chart q i x.val).2)) :
    (timeMap q vertical t x).val ∈ (chart q i).source ∧
      chart q i (timeMap q vertical t x).val = ((chart q i x.val).1, (chart q i x.val).2 + t) := by
  change trajectory q vertical x.val t ∈ (chart q i).source ∧
    chart q i (trajectory q vertical x.val t) = ((chart q i x.val).1, (chart q i x.val).2 + t)
  rw [(vertical_interval q i hR x.val hx hxr).2 t ht]
  have hp : ((chart q i x.val).1, (chart q i x.val).2 + t) ∈ (chart q i).target :=
    hR ⟨hxr.1, by constructor <;> linarith [ht.1, ht.2]⟩
  exact ⟨(chart q i).map_target hp, (chart q i).right_inv hp⟩

theorem base_coordinates {l0 r0 b0 u0 l r b h : ℝ}
    (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) (hx : x.val ∈ base q i l r b)
    {t : ℝ} (ht : t ∈ Icc 0 h) :
    (timeMap q vertical t x).val ∈ (chart q i).source ∧
      chart q i (timeMap q vertical t x).val = ((chart q i x.val).1, b + t) := by
  have hxr : chart q i x.val ∈ rectangle l0 r0 b0 u0 := by
    refine ⟨⟨lt_of_le_of_lt hl hx.2.1.1, lt_of_lt_of_le hx.2.1.2 hr⟩, ?_⟩
    rw [hx.2.2]
    exact ⟨hb, by linarith [ht.1, ht.2]⟩
  have htime : t ∈ Ioo (b0 - (chart q i x.val).2) (u0 - (chart q i x.val).2) := by
    rw [hx.2.2]
    constructor <;> linarith [ht.1, ht.2]
  simpa only [hx.2.2] using coordinates q i hR x hx.1 hxr htime

theorem ordered_gap {l0 r0 b0 u0 l r b h : ℝ}
    (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target)
    (x : CompleteOrbits q vertical) {s t : ℝ}
    (hs : s ∈ hitTimes q i x l r b) (ht : t ∈ hitTimes q i x l r b) (hst : s < t) :
    h < t - s := by
  by_contra hgap
  have htime : t - s ∈ Icc 0 h := ⟨by linarith, le_of_not_gt hgap⟩
  have hc := base_coordinates q i hl hr hb hu hR (timeMap q vertical s x) hs htime
  have heq : timeMap q vertical (t - s) (timeMap q vertical s x) = timeMap q vertical t x := by
    rw [← timeMap_add, sub_add_cancel]
  rw [heq] at hc
  have hy := congrArg Prod.snd hc.2
  change (chart q i (timeMap q vertical t x).val).2 = b + (t - s) at hy
  have hold : (chart q i (timeMap q vertical t x).val).2 = b := ht.2.2
  linarith

theorem separated_hits {l0 r0 b0 u0 l r b h : ℝ}
    (hl : l0 ≤ l) (hr : r ≤ r0) (hb : b0 < b) (hu : b + h < u0)
    (hR : rectangle l0 r0 b0 u0 ⊆ (chart q i).target) (x : CompleteOrbits q vertical) :
    SeparatedWindowCounts.Separated h (hitTimes q i x l r b) := by
  intro s hs t ht hst
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have hgap := ordered_gap q i hl hr hb hu hR x hs ht hlt
    rw [abs_of_neg (sub_neg.mpr hlt)]
    linarith
  · have hgap := ordered_gap q i hl hr hb hu hR x ht hs hgt
    rw [abs_of_pos (sub_pos.mpr hgt)]
    exact hgap

end VeechDichotomy.NativeVerticalFlowboxes
