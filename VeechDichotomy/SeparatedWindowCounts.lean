module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-! Finite counts of uniformly separated real times. Translating a
time set by its separation width changes its count in a bounded closed
window by at most one, with no counting-finiteness premise. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SeparatedWindowCounts

open Set Metric Topology

def Separated (w : ℝ) (A : Set ℝ) : Prop := A.Pairwise (fun x y => w < |x - y|)
def count (A : Set ℝ) (a b : ℝ) : ℕ := (A ∩ Icc a b).ncard

theorem finite_window {A : Set ℝ} {w : ℝ} (hw : 0 < w) (hA : Separated w A) (a b : ℝ) :
    (A ∩ Icc a b).Finite := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have hpair : Pairwise (fun x y : A => w ≤ dist (x : ℝ) (y : ℝ)) := by
    intro x y hxy
    have hval : (x : ℝ) ≠ (y : ℝ) := fun h => hxy (Subtype.ext h)
    simpa only [Real.dist_eq] using (hA x.property y.property hval).le
  have he := Metric.isClosedEmbedding_of_pairwise_le_dist (f := (Subtype.val : A → ℝ)) hw hpair
  have hfin := (he.isCompact_preimage (isCompact_Icc : IsCompact (Icc a b))).finite_of_discrete
  apply (hfin.image (Subtype.val : A → ℝ)).subset
  intro x hx
  exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩

theorem short_interval_subsingleton {A B : Set ℝ} {w : ℝ} (hA : Separated w A)
    (hdiam : ∀ x ∈ B, ∀ y ∈ B, |x - y| ≤ w) : (A ∩ B).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact (not_lt_of_ge (hdiam x hx.2 y hy.2)) (hA hx.1 hy.1 hxy)

theorem shifted_window_bounds {A : Set ℝ} {w : ℝ} (hw : 0 < w) (hA : Separated w A) (a b : ℝ) :
    count A a b ≤ count A (a - w) (b - w) + 1 ∧ count A (a - w) (b - w) ≤ count A a b + 1 := by
  have hright : (A ∩ Ioc (b - w) b).Subsingleton :=
    short_interval_subsingleton hA (fun x hx y hy => abs_le.mpr ⟨by linarith [hx.1, hx.2, hy.1, hy.2], by linarith [hx.1, hx.2, hy.1, hy.2]⟩)
  have hleft : (A ∩ Ico (a - w) a).Subsingleton :=
    short_interval_subsingleton hA (fun x hx y hy => abs_le.mpr ⟨by linarith [hx.1, hx.2, hy.1, hy.2], by linarith [hx.1, hx.2, hy.1, hy.2]⟩)
  have hrightCard : (A ∩ Ioc (b - w) b).ncard ≤ 1 :=
    (ncard_le_one hright.finite).mpr (fun _ hx _ hy => hright hx hy)
  have hleftCard : (A ∩ Ico (a - w) a).ncard ≤ 1 :=
    (ncard_le_one hleft.finite).mpr (fun _ hx _ hy => hleft hx hy)
  have hsubR : A ∩ Icc a b ⊆ (A ∩ Icc (a - w) (b - w)) ∪ (A ∩ Ioc (b - w) b) := by
    intro x hx
    by_cases hxb : x ≤ b - w
    · exact Or.inl ⟨hx.1, by constructor <;> linarith [hx.2.1]⟩
    · exact Or.inr ⟨hx.1, lt_of_not_ge hxb, hx.2.2⟩
  have hsubL : A ∩ Icc (a - w) (b - w) ⊆ (A ∩ Icc a b) ∪ (A ∩ Ico (a - w) a) := by
    intro x hx
    by_cases hxa : a ≤ x
    · exact Or.inl ⟨hx.1, by constructor <;> linarith [hx.2.2]⟩
    · exact Or.inr ⟨hx.1, hx.2.1, lt_of_not_ge hxa⟩
  constructor
  · exact (ncard_le_ncard hsubR ((finite_window hw hA _ _).union hright.finite)).trans
      ((ncard_union_le _ _).trans (Nat.add_le_add_left hrightCard _))
  · exact (ncard_le_ncard hsubL ((finite_window hw hA _ _).union hleft.finite)).trans
      ((ncard_union_le _ _).trans (Nat.add_le_add_left hleftCard _))

theorem translate_window_count {A B : Set ℝ} (w a b : ℝ) (hshift : ∀ t, t ∈ A ↔ t + w ∈ B) :
    count B a b = count A (a - w) (b - w) := by
  have heq : (fun t : ℝ => t + w) '' (A ∩ Icc (a - w) (b - w)) = B ∩ Icc a b := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(hshift s).mp hs.1, by constructor <;> linarith [hs.2.1, hs.2.2]⟩
    · intro ht
      refine ⟨t - w, ⟨?_, by constructor <;> linarith [ht.2.1, ht.2.2]⟩, sub_add_cancel t w⟩
      apply (hshift (t - w)).mpr
      simpa only [sub_add_cancel] using ht.1
  have hinj : Function.Injective (fun t : ℝ => t + w) := fun _ _ h => add_right_cancel h
  unfold count
  rw [← heq, hinj.injOn.ncard_image]

theorem translate_count_bounds {A B : Set ℝ} {w : ℝ} (hw : 0 < w) (hA : Separated w A)
    (hshift : ∀ t, t ∈ A ↔ t + w ∈ B) (a b : ℝ) :
    count A a b ≤ count B a b + 1 ∧ count B a b ≤ count A a b + 1 := by
  rw [translate_window_count w a b hshift]
  exact shifted_window_bounds hw hA a b

end VeechDichotomy.SeparatedWindowCounts
