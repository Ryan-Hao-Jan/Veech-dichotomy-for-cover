module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Set.Card

/-! An actual fundamental domain bounds the measure of a set whose
translates have finite overlap multiplicity. The genuine invariant
integral decomposes over the domain, Tonelli counts the actual orbit
hits, and a relative-element injection bounds their cardinality. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FundamentalDomainMultiplicity

open Set Function MeasureTheory
open scoped ENNReal BigOperators

variable {G X : Type*} [Group G] [MulAction G X]

theorem hits_encard_le (T : Set X) (S : Set G)
    (hrel : ∀ x : X, ∀ g h : G, g • x ∈ T → h • x ∈ T → g * h⁻¹ ∈ S) (x : X) :
    {g : G | g • x ∈ T}.encard ≤ S.encard := by
  let H : Set G := {g | g • x ∈ T}
  change H.encard ≤ S.encard
  rcases H.eq_empty_or_nonempty with he | ⟨h, hh⟩
  · rw [he, encard_empty]
    exact zero_le
  · exact Set.encard_le_encard_of_injOn (f := fun g => g * h⁻¹)
      (fun g hg => hrel x g h hg hh) (fun _ _ _ _ heq => mul_right_cancel heq)

variable [Countable G] [MeasurableSpace X] (μ : Measure X)
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

theorem measure_le {F T : Set X} (hF : IsFundamentalDomain G F μ) (hT : MeasurableSet T)
    (N : ℝ≥0∞) (hbound : ∀ x : X, ({g : G | g • x ∈ T}.encard : ℝ≥0∞) ≤ N) :
    μ T ≤ N * μ F := by
  classical
  let f : X → ℝ≥0∞ := T.indicator (fun _ => 1)
  have hm : Measurable f := measurable_const.indicator hT
  have hpoint (x : X) : (∑' g : G, f (g • x)) = ({g : G | g • x ∈ T}.encard : ℝ≥0∞) := by
    rw [← ENNReal.tsum_set_one, tsum_subtype {g : G | g • x ∈ T} (fun _ : G => (1 : ℝ≥0∞))]
    apply tsum_congr
    intro g
    by_cases hg : g • x ∈ T <;> simp [f, Set.indicator, hg]
  calc
    μ T = ∫⁻ x, f x ∂μ := by
      dsimp only [f]
      rw [lintegral_indicator hT]
      simp
    _ = ∑' g : G, ∫⁻ x in F, f (g • x) ∂μ := hF.lintegral_eq_tsum'' f
    _ = ∫⁻ x in F, ∑' g : G, f (g • x) ∂μ :=
      (lintegral_tsum (fun g => (hm.comp (measurable_const_smul g)).aemeasurable)).symm
    _ ≤ ∫⁻ _x in F, N ∂μ := lintegral_mono (fun x => (hpoint x).le.trans (hbound x))
    _ = N * μ F := by simp

theorem measure_lt_top_of_relative {F T : Set X} (hF : IsFundamentalDomain G F μ)
    (hFfin : μ F < ∞) (hT : MeasurableSet T) (S : Set G) (hS : S.Finite)
    (hrel : ∀ x : X, ∀ g h : G, g • x ∈ T → h • x ∈ T → g * h⁻¹ ∈ S) : μ T < ∞ := by
  have hb := measure_le μ hF hT (S.encard : ℝ≥0∞)
    (fun x => ENat.toENNReal_mono (hits_encard_le T S hrel x))
  exact hb.trans_lt (ENNReal.mul_lt_top (ENat.toENNReal_lt_top.mpr hS.encard_lt_top) hFfin)

end VeechDichotomy.FundamentalDomainMultiplicity
