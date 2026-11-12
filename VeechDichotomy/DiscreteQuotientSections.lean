module

public import VeechDichotomy.MeasurableLocalSections
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Tactic.Group

/-! Genuine measurable representatives for the actual right-coset space
of a discrete subgroup. They give an explicit measurable equivalence
between the group and quotient-times-subgroup, with actual inverse
given by the subgroup coordinate s(g Gamma)^(-1)g. Normality is not used. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DiscreteQuotientSections

open Set Function Topology MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (Γ : Subgroup G) [DiscreteTopology Γ]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

theorem exists_representative : ∃ s : G ⧸ Γ → G, Measurable s ∧
    ∀ x, (QuotientGroup.mk (s x) : G ⧸ Γ) = x := by
  have hdisc : IsDiscrete (Γ : Set G) := SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact MeasurableLocalSections.exists_measurable_rightInverse
    (Γ.isQuotientCoveringMap hdisc).isLocalHomeomorph QuotientGroup.mk_surjective

def representative : G ⧸ Γ → G := Classical.choose (exists_representative Γ)

theorem measurable_representative : Measurable (representative Γ) :=
  (Classical.choose_spec (exists_representative Γ)).1

@[simp] theorem project_representative (x : G ⧸ Γ) :
    (QuotientGroup.mk (representative Γ x) : G ⧸ Γ) = x :=
  (Classical.choose_spec (exists_representative Γ)).2 x

theorem coordinate_mem (g : G) : (representative Γ (QuotientGroup.mk g))⁻¹ * g ∈ Γ :=
  QuotientGroup.eq.mp (project_representative Γ (QuotientGroup.mk g))

def coordinate (g : G) : Γ := ⟨(representative Γ (QuotientGroup.mk g))⁻¹ * g, coordinate_mem Γ g⟩

theorem measurable_coordinate : Measurable (coordinate Γ) := by
  have hm : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'.measurable
  exact (((measurable_representative Γ).comp hm).inv.mul measurable_id).subtype_mk

theorem project_product (x : G ⧸ Γ) (γ : Γ) :
    (QuotientGroup.mk (representative Γ x * (γ : G)) : G ⧸ Γ) = x := by
  apply Eq.trans _ (project_representative Γ x)
  apply QuotientGroup.eq.mpr
  have h : (representative Γ x * (γ : G))⁻¹ * representative Γ x = (γ : G)⁻¹ := by group
  rw [h]
  exact Γ.inv_mem γ.property

def fiberEquiv : ((G ⧸ Γ) × Γ) ≃ᵐ G where
  toFun p := representative Γ p.1 * (p.2 : G)
  invFun g := (QuotientGroup.mk g, coordinate Γ g)
  left_inv p := by
    apply Prod.ext
    · exact project_product Γ p.1 p.2
    · apply Subtype.ext
      change (representative Γ (QuotientGroup.mk (representative Γ p.1 * (p.2 : G))))⁻¹ *
        (representative Γ p.1 * (p.2 : G)) = (p.2 : G)
      rw [project_product]
      group
  right_inv g := by
    change representative Γ (QuotientGroup.mk g) * ((representative Γ (QuotientGroup.mk g))⁻¹ * g) = g
    group
  measurable_toFun := ((measurable_representative Γ).comp measurable_fst).mul
    (measurable_subtype_coe.comp measurable_snd)
  measurable_invFun := continuous_quotient_mk'.measurable.prodMk (measurable_coordinate Γ)

@[simp] theorem fiberEquiv_apply (p : (G ⧸ Γ) × Γ) :
    fiberEquiv Γ p = representative Γ p.1 * (p.2 : G) := rfl

@[simp] theorem fiberEquiv_symm_apply (g : G) :
    (fiberEquiv Γ).symm g = (QuotientGroup.mk g, coordinate Γ g) := rfl

end VeechDichotomy.DiscreteQuotientSections
