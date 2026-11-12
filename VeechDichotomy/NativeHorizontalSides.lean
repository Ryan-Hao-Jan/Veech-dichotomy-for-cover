module

public import VeechDichotomy.NativePrimitiveRectangles

/-! Actual horizontal native trajectories carry vertical sides of a
primitive rectangle to one another. Exact translations of the maximal
trajectory hit-time sets are derived from native flow uniqueness and
the actual chart source, including lifetime statements. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeHorizontalSides

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles
open Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

def side (c b u : ℝ) : Set (Regular q) :=
  {x | x ∈ (chart q i).source ∧ (chart q i x).1 = c ∧ (chart q i x).2 ∈ Ioo b u}

theorem side_transport {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) {x : Regular q} (hx : x ∈ side q i c b u) :
    d - c ∈ domain q horizontal x ∧ trajectory q horizontal x (d - c) ∈ side q i d b u := by
  have hxr : chart q i x ∈ rectangle l r b u := ⟨hx.2.1.symm ▸ hc, hx.2.2⟩
  have ht : d - c ∈ Ioo (l - (chart q i x).1) (r - (chart q i x).1) := by
    rw [hx.2.1]
    constructor <;> linarith [hd.1, hd.2]
  have hseg := horizontal_interval q i hR x hx.1 hxr
  have htarget : ((chart q i x).1 + (d - c), (chart q i x).2) ∈ (chart q i).target := by
    apply hR
    refine ⟨?_, hx.2.2⟩
    rw [hx.2.1]
    simpa only [add_sub_cancel] using hd
  refine ⟨hseg.1 ht, ?_⟩
  rw [hseg.2 _ ht]
  have hcoords := (chart q i).right_inv htarget
  refine ⟨(chart q i).map_target htarget, ?_, ?_⟩
  · have h := congrArg Prod.fst hcoords
    simpa only [Prod.fst, hx.2.1, add_sub_cancel] using h
  · simpa only [congrArg Prod.snd hcoords] using hx.2.2

def hitTimes (x : Regular q) (c b u : ℝ) : Set ℝ :=
  {t | t ∈ domain q horizontal x ∧ trajectory q horizontal x t ∈ side q i c b u}

theorem hit_shift {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) {t : ℝ}
    (ht : t ∈ hitTimes q i x c b u) : t + (d - c) ∈ hitTimes q i x d b u := by
  have hstep := side_transport q i hc hd hR ht.2
  have htime := hstep.1
  rw [domain_at_time q horizontal x t ht.1] at htime
  have hflow := trajectory_add q horizontal x t ht.1 (d - c) hstep.1
  refine ⟨by simpa only [mem_ofPred_eq, add_comm] using htime, ?_⟩
  rw [add_comm t (d - c), ← hflow]
  exact hstep.2

theorem hit_shift_iff {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) (x : Regular q) (t : ℝ) :
    t ∈ hitTimes q i x c b u ↔ t + (d - c) ∈ hitTimes q i x d b u := by
  refine ⟨hit_shift q i hc hd hR x, ?_⟩
  intro ht
  have hback := hit_shift q i hd hc hR x ht
  have heq : t + (d - c) + (c - d) = t := by ring
  simpa only [heq] using hback

end VeechDichotomy.NativeHorizontalSides
