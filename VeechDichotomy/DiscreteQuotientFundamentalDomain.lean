module

public import VeechDichotomy.DiscreteQuotientMeasureLift
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-! A genuine measurable fundamental domain for the actual right action
of a discrete subgroup, constructed from the proved measurable section.
Every group element has exactly one right translate in the domain. The
counting-fiber lift assigns it precisely the total quotient mass.
Neither existence nor volume of this fundamental domain is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DiscreteQuotientFundamentalDomain

open DiscreteQuotientSections DiscreteQuotientMeasureLift Set Function Topology MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (Γ : Subgroup G) [DiscreteTopology Γ]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

theorem coordinate_product (x : G ⧸ Γ) (γ : Γ) :
    coordinate Γ (representative Γ x * (γ : G)) = γ :=
  congrArg Prod.snd ((fiberEquiv Γ).symm_apply_apply (x, γ))

theorem reconstruct (g : G) : representative Γ (QuotientGroup.mk g) * (coordinate Γ g : G) = g :=
  (fiberEquiv Γ).apply_symm_apply g

theorem coordinate_mul (g : G) (δ : Γ) : coordinate Γ (g * (δ : G)) = coordinate Γ g * δ := by
  calc
    coordinate Γ (g * (δ : G)) = coordinate Γ (representative Γ (QuotientGroup.mk g) *
        ((coordinate Γ g * δ : Γ) : G)) := by
      congr 1
      rw [Subgroup.coe_mul, ← mul_assoc, reconstruct]
    _ = coordinate Γ g * δ := coordinate_product Γ _ _

def domain : Set G := coordinate Γ ⁻¹' {1}

theorem measurable_domain : MeasurableSet (domain Γ) :=
  (measurable_coordinate Γ) (measurableSet_singleton 1)

theorem domain_eq_range : domain Γ = range (representative Γ) := by
  ext g
  constructor
  · intro hg
    have hc : coordinate Γ g = 1 := hg
    refine ⟨QuotientGroup.mk g, ?_⟩
    have h := reconstruct Γ g
    simpa only [hc, Subgroup.coe_one, mul_one] using h
  · rintro ⟨x, rfl⟩
    change coordinate Γ (representative Γ x) = 1
    simpa only [Subgroup.coe_one, mul_one] using coordinate_product Γ x 1

theorem unique_translate (g : G) : ∃! δ : Γ.op, δ • g ∈ domain Γ := by
  let δ : Γ.op := ⟨MulOpposite.op ((coordinate Γ g : G)⁻¹), Γ.inv_mem (coordinate Γ g).property⟩
  refine ⟨δ, ?_, ?_⟩
  · change coordinate Γ (g * (((coordinate Γ g)⁻¹ : Γ) : G)) = 1
    rw [coordinate_mul, mul_inv_cancel]
  · intro η hη
    let ε : Γ := ⟨MulOpposite.unop (η : Gᵐᵒᵖ), η.property⟩
    have hc : coordinate Γ (g * (ε : G)) = 1 := hη
    have hm : coordinate Γ g * ε = 1 := (coordinate_mul Γ g ε).symm.trans hc
    have he : ε = (coordinate Γ g)⁻¹ := by
      calc
        ε = (coordinate Γ g)⁻¹ * (coordinate Γ g * ε) := by group
        _ = (coordinate Γ g)⁻¹ := by rw [hm, mul_one]
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val he

theorem isFundamentalDomain (μ : Measure G) : IsFundamentalDomain Γ.op (domain Γ) μ :=
  IsFundamentalDomain.mk' (measurable_domain Γ).nullMeasurableSet (unique_translate Γ)

variable [Countable Γ]

theorem measure_domain (μ : Measure (G ⧸ Γ)) : lift Γ μ (domain Γ) = μ univ := by
  rw [lift, Measure.map_apply (fiberEquiv Γ).measurable (measurable_domain Γ),
    Measure.prod_apply ((fiberEquiv Γ).measurable (measurable_domain Γ))]
  have hset (x : G ⧸ Γ) : Prod.mk x ⁻¹' (fiberEquiv Γ ⁻¹' domain Γ) = ({1} : Set Γ) := by
    ext γ
    change coordinate Γ (representative Γ x * (γ : G)) = 1 ↔ γ = 1
    rw [coordinate_product]
  simp only [hset, Measure.count_singleton, lintegral_const, one_mul]

end VeechDichotomy.DiscreteQuotientFundamentalDomain
