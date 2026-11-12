module

public import VeechDichotomy.DiscreteQuotientSections
public import Mathlib.MeasureTheory.Group.Action

/-! Lift a measure from an actual discrete subgroup quotient by counting
the actual subgroup coordinate. The lift of an invariant measure is left
invariant on the group. The proof computes the genuine section cocycle
and uses measure preservation of its skew product with counting measure.
No normality, Haar identification or fundamental domain is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DiscreteQuotientMeasureLift

open DiscreteQuotientSections Set Function Topology MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (Γ : Subgroup G) [DiscreteTopology Γ]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

def cocycle (g : G) (x : G ⧸ Γ) : Γ := coordinate Γ (g * representative Γ x)

theorem measurable_cocycle (g : G) : Measurable (cocycle Γ g) :=
  (measurable_coordinate Γ).comp (measurable_const.mul (measurable_representative Γ))

theorem cocycle_relation (g : G) (x : G ⧸ Γ) :
    representative Γ (g • x) * (cocycle Γ g x : G) = g * representative Γ x := by
  have hproj : (QuotientGroup.mk (g * representative Γ x) : G ⧸ Γ) = g • x := by
    change g • (QuotientGroup.mk (representative Γ x) : G ⧸ Γ) = g • x
    rw [project_representative]
  change representative Γ (g • x) * ((representative Γ
    (QuotientGroup.mk (g * representative Γ x)))⁻¹ * (g * representative Γ x)) = _
  rw [hproj]
  group

def skew (g : G) (p : (G ⧸ Γ) × Γ) : (G ⧸ Γ) × Γ :=
  (g • p.1, cocycle Γ g p.1 * p.2)

theorem measurable_skew (g : G) : Measurable (skew Γ g) :=
  ((measurable_const_smul g).comp measurable_fst).prodMk
    (((measurable_cocycle Γ g).comp measurable_fst).mul measurable_snd)

theorem fiberEquiv_skew (g : G) (p : (G ⧸ Γ) × Γ) :
    fiberEquiv Γ (skew Γ g p) = g * fiberEquiv Γ p := by
  change representative Γ (g • p.1) * ((cocycle Γ g p.1 : G) * (p.2 : G)) =
    g * (representative Γ p.1 * (p.2 : G))
  rw [← mul_assoc, cocycle_relation]
  group

def lift (μ : Measure (G ⧸ Γ)) : Measure G := (μ.prod Measure.count).map (fiberEquiv Γ)

variable [Countable Γ] (μ : Measure (G ⧸ Γ)) [SFinite μ]
  [SMulInvariantMeasure G (G ⧸ Γ) μ]

theorem measurePreserving_skew (g : G) :
    MeasurePreserving (skew Γ g) (μ.prod Measure.count) (μ.prod Measure.count) := by
  change MeasurePreserving (fun p : (G ⧸ Γ) × Γ => (g • p.1, cocycle Γ g p.1 * p.2)) _ _
  apply (measurePreserving_smul g μ).skew_product (g := fun x γ => cocycle Γ g x * γ)
    (((measurable_cocycle Γ g).comp measurable_fst).mul measurable_snd)
  exact Filter.Eventually.of_forall (fun x => map_mul_left_eq_self Measure.count (cocycle Γ g x))

instance lift_leftInvariant : (lift Γ μ).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    change ((μ.prod Measure.count).map (fiberEquiv Γ)).map (fun z => g * z) =
      (μ.prod Measure.count).map (fiberEquiv Γ)
    rw [Measure.map_map (measurable_const_mul g) (fiberEquiv Γ).measurable]
    have heq : (fun z => g * z) ∘ fiberEquiv Γ = fiberEquiv Γ ∘ skew Γ g := by
      funext p
      exact (fiberEquiv_skew Γ g p).symm
    rw [heq, ← Measure.map_map (fiberEquiv Γ).measurable (measurable_skew Γ g),
      (measurePreserving_skew Γ μ g).map_eq]

end VeechDichotomy.DiscreteQuotientMeasureLift
