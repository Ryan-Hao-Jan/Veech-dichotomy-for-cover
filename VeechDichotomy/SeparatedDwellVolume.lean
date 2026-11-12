module

public import VeechDichotomy.SeparatedWindowCounts
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Positivity

/-! A separated collection of visits spends exactly one block of length `h`
per crossing, except for at most one partial block at either endpoint.
These estimates concern the actual Lebesgue measure of the union of blocks. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.SeparatedDwellVolume

open Set MeasureTheory
open SeparatedWindowCounts
open scoped ENNReal

def blocks (A : Set ℝ) (h : ℝ) : Set ℝ := ⋃ s ∈ A, Ioo s (s + h)

theorem disjoint_blocks {A : Set ℝ} {h : ℝ} (hA : Separated h A) :
    A.PairwiseDisjoint (fun s => Ioo s (s + h)) := by
  intro s hs t ht hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  change s < x ∧ x < s + h at hx
  change t < x ∧ x < t + h at hy
  have hgap := hA hs ht hst
  have habs : |s - t| < h := abs_lt.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
  exact (not_lt_of_ge hgap.le) habs

theorem finite_blocks_volume {A : Set ℝ} {h : ℝ}
    (hA : Separated h A) (hfin : A.Finite) :
    volume (blocks A h) = (A.ncard : ℝ≥0∞) * ENNReal.ofReal h := by
  classical
  have hunion : blocks A h = ⋃ s ∈ hfin.toFinset, Ioo s (s + h) := by
    simp [blocks, hfin.mem_toFinset]
  rw [hunion, measure_biUnion_finset]
  · simp [Real.volume_Ioo, ncard_eq_toFinset_card A hfin]
  · simpa only [hfin.coe_toFinset] using disjoint_blocks hA
  · intro s hs
    exact measurableSet_Ioo

theorem finite_blocks_real {A : Set ℝ} {h : ℝ} (hh : 0 < h)
    (hA : Separated h A) (hfin : A.Finite) :
    volume.real (blocks A h) = h * (A.ncard : ℝ) := by
  rw [Measure.real, finite_blocks_volume hA hfin]
  simp [ENNReal.toReal_mul, hh.le, mul_comm]

theorem finite_blocks_ne_top {A : Set ℝ} {h : ℝ}
    (hA : Separated h A) (hfin : A.Finite) : volume (blocks A h) ≠ ⊤ := by
  rw [finite_blocks_volume hA hfin]
  finiteness

theorem window_bounds {A : Set ℝ} {h : ℝ} (hh : 0 < h) (hA : Separated h A)
    (a b : ℝ) :
    h * (count A a b : ℝ) ≤ volume.real (blocks A h ∩ Ioc a b) + h ∧
      volume.real (blocks A h ∩ Ioc a b) ≤ h * (count A a b : ℝ) + h := by
  have hsmall : Separated h (A ∩ Icc a (b - h)) := hA.mono inter_subset_left
  have hlarge : Separated h (A ∩ Icc (a - h) b) := hA.mono inter_subset_left
  have hlo : blocks (A ∩ Icc a (b - h)) h ⊆ blocks A h ∩ Ioc a b := by
    intro t ht
    rcases mem_iUnion₂.mp ht with ⟨s, hs, hst⟩
    exact ⟨mem_iUnion₂.mpr ⟨s, hs.1, hst⟩,
      by constructor <;> linarith [hs.2.1, hs.2.2, hst.1, hst.2]⟩
  have hhi : blocks A h ∩ Ioc a b ⊆ blocks (A ∩ Icc (a - h) b) h := by
    rintro t ⟨ht, htab⟩
    rcases mem_iUnion₂.mp ht with ⟨s, hs, hst⟩
    exact mem_iUnion₂.mpr ⟨s, ⟨hs,
      by constructor <;> linarith [htab.1, htab.2, hst.1, hst.2]⟩, hst⟩
  have hright : (A ∩ Ioc (b - h) b).Subsingleton :=
    short_interval_subsingleton hA (fun x hx y hy =>
      abs_le.mpr ⟨by linarith [hx.1, hx.2, hy.1, hy.2],
        by linarith [hx.1, hx.2, hy.1, hy.2]⟩)
  have hleft : (A ∩ Ico (a - h) a).Subsingleton :=
    short_interval_subsingleton hA (fun x hx y hy =>
      abs_le.mpr ⟨by linarith [hx.1, hx.2, hy.1, hy.2],
        by linarith [hx.1, hx.2, hy.1, hy.2]⟩)
  have hrc : (A ∩ Ioc (b - h) b).ncard ≤ 1 :=
    (ncard_le_one hright.finite).mpr (fun _ hx _ hy => hright hx hy)
  have hlc : (A ∩ Ico (a - h) a).ncard ≤ 1 :=
    (ncard_le_one hleft.finite).mpr (fun _ hx _ hy => hleft hx hy)
  have hsubR : A ∩ Icc a b ⊆ (A ∩ Icc a (b - h)) ∪ (A ∩ Ioc (b - h) b) := by
    intro s hs
    by_cases hsb : s ≤ b - h
    · exact Or.inl ⟨hs.1, hs.2.1, hsb⟩
    · exact Or.inr ⟨hs.1, lt_of_not_ge hsb, hs.2.2⟩
  have hsubL : A ∩ Icc (a - h) b ⊆ (A ∩ Icc a b) ∪ (A ∩ Ico (a - h) a) := by
    intro s hs
    by_cases hsa : a ≤ s
    · exact Or.inl ⟨hs.1, hsa, hs.2.2⟩
    · exact Or.inr ⟨hs.1, hs.2.1, lt_of_not_ge hsa⟩
  have hcR : count A a b ≤ (A ∩ Icc a (b - h)).ncard + 1 :=
    (ncard_le_ncard hsubR ((finite_window hh hA _ _).union hright.finite)).trans
      ((ncard_union_le _ _).trans (Nat.add_le_add_left hrc _))
  have hcL : (A ∩ Icc (a - h) b).ncard ≤ count A a b + 1 :=
    (ncard_le_ncard hsubL ((finite_window hh hA _ _).union hleft.finite)).trans
      ((ncard_union_le _ _).trans (Nat.add_le_add_left hlc _))
  have hvlo := measureReal_mono (μ := volume) hlo
    (measure_ne_top_of_subset inter_subset_right (by simp))
  have hvhi := measureReal_mono (μ := volume) hhi
    (finite_blocks_ne_top hlarge (finite_window hh hA _ _))
  rw [finite_blocks_real hh hsmall (finite_window hh hA _ _)] at hvlo
  rw [finite_blocks_real hh hlarge (finite_window hh hA _ _)] at hvhi
  constructor
  · have hc : (count A a b : ℝ) ≤ ((A ∩ Icc a (b - h)).ncard : ℝ) + 1 := by exact_mod_cast hcR
    nlinarith
  · have hc : ((A ∩ Icc (a - h) b).ncard : ℝ) ≤ (count A a b : ℝ) + 1 := by exact_mod_cast hcL
    nlinarith

theorem window_error {A : Set ℝ} {h : ℝ} (hh : 0 < h) (hA : Separated h A)
    (a b : ℝ) :
    |volume.real (blocks A h ∩ Ioc a b) - h * (count A a b : ℝ)| ≤ h := by
  have hb := window_bounds hh hA a b
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

end VeechDichotomy.SeparatedDwellVolume
