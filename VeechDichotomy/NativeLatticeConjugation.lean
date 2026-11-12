module

public import VeechDichotomy.NativeLatticeQuotient
public import Mathlib.MeasureTheory.Group.Action

/-! The actual native lattice hypothesis is invariant under genuine
ambient conjugation. Right translation of coset representatives gives
a continuous equivariant map and transports the actual invariant
probability measure; conjugation preserves subgroup discreteness. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeLatticeConjugation

open LinearGroup NativeVeech MeasureTheory Topology

set_option backward.isDefEq.respectTransparency false

def conjugate (Γ : Subgroup SL2) (B : SL2) : Subgroup SL2 where
  carrier := {x | B⁻¹ * x * B ∈ Γ}
  one_mem' := by
    change B⁻¹ * 1 * B ∈ Γ
    simpa only [mul_one, inv_mul_cancel] using Γ.one_mem
  mul_mem' := by
    intro x y hx hy
    change B⁻¹ * (x * y) * B ∈ Γ
    have he : B⁻¹ * (x * y) * B = (B⁻¹ * x * B) * (B⁻¹ * y * B) := by group
    rw [he]
    exact Γ.mul_mem hx hy
  inv_mem' := by
    intro x hx
    change B⁻¹ * x⁻¹ * B ∈ Γ
    have he : B⁻¹ * x⁻¹ * B = (B⁻¹ * x * B)⁻¹ := by group
    rw [he]
    exact Γ.inv_mem hx

def toOriginal (Γ : Subgroup SL2) (B : SL2) (γ : conjugate Γ B) : Γ :=
  ⟨B⁻¹ * (γ : SL2) * B, γ.property⟩

theorem continuous_toOriginal (Γ : Subgroup SL2) (B : SL2) : Continuous (toOriginal Γ B) := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem toOriginal_injective (Γ : Subgroup SL2) (B : SL2) : Function.Injective (toOriginal Γ B) := by
  intro γ δ he
  have hc : B⁻¹ * (γ : SL2) * B = B⁻¹ * (δ : SL2) * B := congrArg Subtype.val he
  apply Subtype.ext
  calc
    (γ : SL2) = B * (B⁻¹ * (γ : SL2) * B) * B⁻¹ := by group
    _ = B * (B⁻¹ * (δ : SL2) * B) * B⁻¹ := by rw [hc]
    _ = (δ : SL2) := by group

theorem discrete_conjugate (Γ : Subgroup SL2) [DiscreteTopology Γ] (B : SL2) :
    DiscreteTopology (conjugate Γ B) :=
  DiscreteTopology.of_continuous_injective (continuous_toOriginal Γ B) (toOriginal_injective Γ B)

def quotientMap (Γ : Subgroup SL2) (B : SL2) : SL2 ⧸ Γ → SL2 ⧸ conjugate Γ B :=
  Quotient.lift (fun g => QuotientGroup.mk (g * B⁻¹)) (by
    intro g h hrel
    apply QuotientGroup.eq.mpr
    change B⁻¹ * ((g * B⁻¹)⁻¹ * (h * B⁻¹)) * B ∈ Γ
    have he : B⁻¹ * ((g * B⁻¹)⁻¹ * (h * B⁻¹)) * B = g⁻¹ * h := by group
    rw [he]
    exact QuotientGroup.leftRel_apply.mp hrel)

theorem continuous_quotientMap (Γ : Subgroup SL2) (B : SL2) : Continuous (quotientMap Γ B) := by
  apply (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  change Continuous (fun g : SL2 => (QuotientGroup.mk (g * B⁻¹) : SL2 ⧸ conjugate Γ B))
  exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)

theorem quotientMap_smul (Γ : Subgroup SL2) (B g : SL2) (x : SL2 ⧸ Γ) :
    quotientMap Γ B (g • x) = g • quotientMap Γ B x := by
  refine Quotient.inductionOn x ?_
  intro h
  change (QuotientGroup.mk ((g * h) * B⁻¹) : SL2 ⧸ conjugate Γ B) = QuotientGroup.mk (g * (h * B⁻¹))
  rw [mul_assoc]

theorem isLattice_conjugate (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (B : SL2) : IsLattice (conjugate Γ B) := by
  let : DiscreteTopology Γ := hΓ.1
  refine ⟨discrete_conjugate Γ B, ?_⟩
  obtain ⟨μ, hprob, hinv⟩ := hΓ.2
  let : IsProbabilityMeasure μ := hprob
  let : SMulInvariantMeasure SL2 (SL2 ⧸ Γ) μ := hinv
  have hm := (continuous_quotientMap Γ B).measurable
  exact ⟨μ.map (quotientMap Γ B), (by infer_instance),
    smulInvariantMeasure_map μ _ (quotientMap_smul Γ B) hm⟩

end VeechDichotomy.NativeLatticeConjugation
