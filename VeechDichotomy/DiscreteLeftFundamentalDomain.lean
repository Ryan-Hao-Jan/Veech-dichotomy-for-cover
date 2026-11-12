module

public import VeechDichotomy.DiscreteQuotientFundamentalDomain

/-! Inversion turns the constructed right-lattice representatives into
an actual measurable left fundamental domain. Its mass for the inverted
counting-fiber lift is exactly the total quotient mass. The pointwise
unique-translate proof works for every measure, including geometric Haar
volumes subsequently compared with the native lift. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DiscreteLeftFundamentalDomain

open DiscreteQuotientSections DiscreteQuotientMeasureLift
open DiscreteQuotientFundamentalDomain Set Function Topology MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (Γ : Subgroup G) [DiscreteTopology Γ]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

def leftDomain : Set G := Inv.inv ⁻¹' domain Γ

theorem measurable_leftDomain : MeasurableSet (leftDomain Γ) :=
  measurable_inv (measurable_domain Γ)

theorem unique_translate (g : G) : ∃! γ : Γ, γ • g ∈ leftDomain Γ := by
  let γ : Γ := coordinate Γ g⁻¹
  refine ⟨γ, ?_, ?_⟩
  · change coordinate Γ (((γ : G) * g)⁻¹) = 1
    rw [mul_inv_rev]
    change coordinate Γ (g⁻¹ * (((coordinate Γ g⁻¹)⁻¹ : Γ) : G)) = 1
    rw [coordinate_mul, mul_inv_cancel]
  · intro η hη
    have hc : coordinate Γ (g⁻¹ * ((η⁻¹ : Γ) : G)) = 1 := by
      change coordinate Γ (((η : G) * g)⁻¹) = 1 at hη
      simpa only [mul_inv_rev, Subgroup.coe_inv] using hη
    have hm : coordinate Γ g⁻¹ * η⁻¹ = 1 := (coordinate_mul Γ g⁻¹ η⁻¹).symm.trans hc
    have he : coordinate Γ g⁻¹ = η := by
      calc
        coordinate Γ g⁻¹ = (coordinate Γ g⁻¹ * η⁻¹) * η := by group
        _ = η := by rw [hm, one_mul]
    exact he.symm

theorem isFundamentalDomain (μ : Measure G) : IsFundamentalDomain Γ (leftDomain Γ) μ :=
  IsFundamentalDomain.mk' (measurable_leftDomain Γ).nullMeasurableSet (unique_translate Γ)

variable [Countable Γ]

theorem inv_lift_mass (μ : Measure (G ⧸ Γ)) : (lift Γ μ).inv (leftDomain Γ) = μ univ := by
  rw [Measure.inv_apply]
  have hinv : (leftDomain Γ)⁻¹ = domain Γ := by
    ext g
    change (g⁻¹)⁻¹ ∈ domain Γ ↔ g ∈ domain Γ
    rw [inv_inv]
  rw [hinv, measure_domain]

end VeechDichotomy.DiscreteLeftFundamentalDomain
