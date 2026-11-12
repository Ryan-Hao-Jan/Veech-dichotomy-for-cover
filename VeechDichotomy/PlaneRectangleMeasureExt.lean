module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Finite plane measures are determined by open coordinate rectangles.
The rational rectangle pi-system and its explicit countable spanning
family discharge measure extensionality, rather than assuming that an
arbitrary topological basis determines measures. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PlaneRectangleMeasureExt

open MeasureTheory Set

theorem ext {μ ν : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h : ∀ l r b t : ℝ, μ (Ioo l r ×ˢ Ioo b t) = ν (Ioo l r ×ˢ Ioo b t)) : μ = ν := by
  let H := Real.finiteSpanningSetsInIooRat (volume : Measure ℝ)
  apply Measure.ext_of_generateFrom_of_iUnion _ (H.prod H).set
    (generateFrom_eq_prod Real.borel_eq_generateFrom_Ioo_rat.symm Real.borel_eq_generateFrom_Ioo_rat.symm
      H.isCountablySpanning H.isCountablySpanning).symm
    (Real.isPiSystem_Ioo_rat.prod Real.isPiSystem_Ioo_rat) (H.prod H).spanning (H.prod H).set_mem
    (fun _ => measure_ne_top _ _)
  rintro s ⟨u, hu, v, hv, rfl⟩
  simp only [mem_iUnion, mem_singleton_iff] at hu hv
  obtain ⟨a, b, _, rfl⟩ := hu
  obtain ⟨c, d, _, rfl⟩ := hv
  exact h a b c d

theorem codRestrict_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (S : Set β) (hS : ∀ a, f a ∈ S) :
    MeasurableEmbedding (fun a => (⟨f a, hS a⟩ : S)) := by
  refine ⟨fun a b hab => hf.injective (congrArg Subtype.val hab), hf.measurable.subtype_mk, ?_⟩
  intro U hU
  have heq : (fun a => (⟨f a, hS a⟩ : S)) '' U = (Subtype.val : S → β) ⁻¹' (f '' U) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hay⟩
      exact ⟨a, ha, Subtype.ext hay⟩
  rw [heq]
  exact (hf.measurableSet_image' hU).preimage measurable_subtype_coe

end VeechDichotomy.PlaneRectangleMeasureExt
