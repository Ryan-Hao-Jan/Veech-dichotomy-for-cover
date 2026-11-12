module

public import VeechDichotomy.DiscreteQuotientMeasureLift
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Regular

/-! The actual counting-fiber lift of an invariant quotient probability
is a Haar measure on the group. Local quotient charts bound its mass by
the quotient mass, proving local finiteness. A product set with singleton
subgroup coordinate proves nonzero mass. No normality or Haar comparison
is supplied as an assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DiscreteQuotientLiftHaar

open DiscreteQuotientSections DiscreteQuotientMeasureLift Set Filter Topology MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (Γ : Subgroup G) [DiscreteTopology Γ]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

theorem fiber_subsingleton {U : Set G} (hU : InjOn (QuotientGroup.mk : G → G ⧸ Γ) U)
    (x : G ⧸ Γ) : {γ : Γ | representative Γ x * (γ : G) ∈ U}.Subsingleton := by
  intro γ hγ δ hδ
  apply Subtype.ext
  apply mul_left_cancel (a := representative Γ x)
  apply hU hγ hδ
  exact (project_product Γ x γ).trans (project_product Γ x δ).symm

theorem count_fiber_le_one {U : Set G} (hU : InjOn (QuotientGroup.mk : G → G ⧸ Γ) U)
    (x : G ⧸ Γ) : Measure.count {γ : Γ | representative Γ x * (γ : G) ∈ U} ≤ 1 := by
  let S : Set Γ := {γ | representative Γ x * (γ : G) ∈ U}
  change Measure.count S ≤ 1
  have hs : S.Subsingleton := fiber_subsingleton Γ hU x
  rcases S.eq_empty_or_nonempty with hzero | ⟨γ, hγ⟩
  · simp only [hzero, measure_empty, zero_le]
  · calc
      Measure.count S ≤ Measure.count {γ} := measure_mono (fun δ hδ => hs hδ hγ)
      _ = 1 := Measure.count_singleton γ

variable [Countable Γ] (μ : Measure (G ⧸ Γ))

theorem lift_le_of_injOn {U : Set G} (hUm : MeasurableSet U)
    (hU : InjOn (QuotientGroup.mk : G → G ⧸ Γ) U) : lift Γ μ U ≤ μ univ := by
  rw [lift, Measure.map_apply (fiberEquiv Γ).measurable hUm,
    Measure.prod_apply ((fiberEquiv Γ).measurable hUm)]
  calc
    (∫⁻ x, Measure.count (Prod.mk x ⁻¹' (fiberEquiv Γ ⁻¹' U)) ∂μ) ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂μ :=
      lintegral_mono (fun x => count_fiber_le_one Γ hU x)
    _ = μ univ := by simp

variable [IsProbabilityMeasure μ]

theorem lift_ne_zero : lift Γ μ ≠ 0 := by
  intro hzero
  have hbound : (1 : ℝ≥0∞) ≤ lift Γ μ univ := by
    calc
      1 = (μ.prod (Measure.count : Measure Γ)) (univ ×ˢ {1}) := by simp
      _ ≤ (μ.prod (Measure.count : Measure Γ)) univ := measure_mono (subset_univ _)
      _ = lift Γ μ univ := by
        rw [lift, Measure.map_apply (fiberEquiv Γ).measurable MeasurableSet.univ, preimage_univ]
  simp [hzero] at hbound

instance lift_locallyFinite : IsLocallyFiniteMeasure (lift Γ μ) where
  finiteAtNhds g := by
    have hdisc : IsDiscrete (Γ : Set G) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
    have hlocal : IsLocalHomeomorph (QuotientGroup.mk : G → G ⧸ Γ) :=
      (Γ.isQuotientCoveringMap hdisc).isLocalHomeomorph
    obtain ⟨e, he, heq⟩ := hlocal g
    have hinj : InjOn (QuotientGroup.mk : G → G ⧸ Γ) e.source := by rw [heq]; exact e.injOn
    refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
    exact (lift_le_of_injOn Γ μ e.open_source.measurableSet hinj).trans_lt (by simp)

variable [T2Space G] [LocallyCompactSpace G] [TopologicalSpace.PseudoMetrizableSpace G]
  [SMulInvariantMeasure G (G ⧸ Γ) μ]

instance lift_haar : Measure.IsHaarMeasure (lift Γ μ) := by
  let : NeZero (lift Γ μ) := ⟨lift_ne_zero Γ μ⟩
  exact { toIsFiniteMeasureOnCompacts := inferInstance
          toIsMulLeftInvariant := inferInstance
          toIsOpenPosMeasure := inferInstance }

end VeechDichotomy.DiscreteQuotientLiftHaar
