module

public import VeechDichotomy.NativeHorizontalHitSeparation

/-! Opposite-side transport and count bounds with an arbitrary common
height set, including CLOSED vertical segments. The height coordinate
is proved to be preserved by the actual horizontal flow. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeHorizontalSlices

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveAreaCharts MNEC.NativeDirectionalDynamics NativePrimitiveRectangles NativeHorizontalSides
open Set Filter Topology
open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X) (i : Index q)

theorem transport_height {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) {x : Regular q} (hx : x ∈ side q i c b u) :
    (chart q i (trajectory q horizontal x (d - c))).2 = (chart q i x).2 := by
  have hxr : chart q i x ∈ rectangle l r b u := ⟨hx.2.1.symm ▸ hc, hx.2.2⟩
  have ht : d - c ∈ Ioo (l - (chart q i x).1) (r - (chart q i x).1) := by
    rw [hx.2.1]
    constructor <;> linarith [hd.1, hd.2]
  have htarget : ((chart q i x).1 + (d - c), (chart q i x).2) ∈ (chart q i).target := by
    apply hR
    refine ⟨?_, hx.2.2⟩
    rw [hx.2.1]
    simpa only [add_sub_cancel] using hd
  rw [(horizontal_interval q i hR x hx.1 hxr).2 _ ht]
  have h := congrArg Prod.snd ((chart q i).right_inv htarget)
  simpa only [Prod.snd] using h

def slice (c : ℝ) (J : Set ℝ) : Set (Regular q) :=
  {x | x ∈ (chart q i).source ∧ (chart q i x).1 = c ∧ (chart q i x).2 ∈ J}

theorem slice_subset_side {c b u : ℝ} {J : Set ℝ} (hJ : J ⊆ Ioo b u) :
    slice q i c J ⊆ side q i c b u := fun _ hx => ⟨hx.1, hx.2.1, hJ hx.2.2⟩

theorem slice_transport {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b u)
    {x : Regular q} (hx : x ∈ slice q i c J) :
    d - c ∈ domain q horizontal x ∧ trajectory q horizontal x (d - c) ∈ slice q i d J := by
  have hside := slice_subset_side q i hJ hx
  have hstep := side_transport q i hc hd hR hside
  refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, ?_⟩
  rw [transport_height q i hc hd hR hside]
  exact hx.2.2

def hits (x : Regular q) (c : ℝ) (J : Set ℝ) : Set ℝ :=
  {t | t ∈ domain q horizontal x ∧ trajectory q horizontal x t ∈ slice q i c J}

theorem hits_subset {c b u : ℝ} {J : Set ℝ} (hJ : J ⊆ Ioo b u) (x : Regular q) :
    hits q i x c J ⊆ hitTimes q i x c b u := fun _ ht => ⟨ht.1, slice_subset_side q i hJ ht.2⟩

theorem hits_shift {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b u)
    (x : Regular q) {t : ℝ} (ht : t ∈ hits q i x c J) : t + (d - c) ∈ hits q i x d J := by
  have hstep := slice_transport q i hc hd hR hJ ht.2
  have htime := (hit_shift q i hc hd hR x (hits_subset q i hJ x ht)).1
  have hflow := trajectory_add q horizontal x t ht.1 (d - c) hstep.1
  refine ⟨htime, ?_⟩
  rw [add_comm t (d - c), ← hflow]
  exact hstep.2

theorem hits_shift_iff {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b u)
    (x : Regular q) (t : ℝ) : t ∈ hits q i x c J ↔ t + (d - c) ∈ hits q i x d J := by
  refine ⟨hits_shift q i hc hd hR hJ x, ?_⟩
  intro ht
  have hback := hits_shift q i hd hc hR hJ x ht
  have heq : t + (d - c) + (c - d) = t := by ring
  simpa only [heq] using hback

theorem hits_separated {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r)
    (hR : rectangle l r b u ⊆ (chart q i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b u) (x : Regular q) :
    SeparatedWindowCounts.Separated (d - c) (hits q i x c J) := by
  intro s hs t ht hst
  exact NativeHorizontalHitSeparation.separated q i hc hd hR x (hits_subset q i hJ x hs) (hits_subset q i hJ x ht) hst

theorem count_bounds {l r b u c d : ℝ} (hc : c ∈ Ioo l r) (hd : d ∈ Ioo l r) (hcd : c < d)
    (hR : rectangle l r b u ⊆ (chart q i).target) {J : Set ℝ} (hJ : J ⊆ Ioo b u)
    (x : Regular q) (a z : ℝ) :
    SeparatedWindowCounts.count (hits q i x c J) a z ≤ SeparatedWindowCounts.count (hits q i x d J) a z + 1 ∧
      SeparatedWindowCounts.count (hits q i x d J) a z ≤ SeparatedWindowCounts.count (hits q i x c J) a z + 1 :=
  SeparatedWindowCounts.translate_count_bounds (sub_pos.mpr hcd) (hits_separated q i hc hd hR hJ x)
    (hits_shift_iff q i hc hd hR hJ x) a z

end VeechDichotomy.NativeHorizontalSlices
