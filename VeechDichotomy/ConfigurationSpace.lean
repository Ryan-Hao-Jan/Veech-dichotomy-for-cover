module

public import VeechDichotomy.Configuration
public import VeechDichotomy.MarkedOrbit

/-! The topological space of distinct ordered tuples itself, with its
induced action. This permits marked deformations to be formed inside the
distinct-mark locus throughout, rather than only in its ambient product.
-/

@[expose] public section

open Set Topology

namespace VeechDichotomy

abbrev ConfigurationSpace (m : ℕ) (X : Type*) := configuration m X

variable {X G : Type*} {m : ℕ} [Group G] [MulAction G X]

instance configurationSpaceAction : MulAction G (ConfigurationSpace m X) where
  smul g b := ⟨g • b.val, invariant_configuration g b.property⟩
  one_smul b := Subtype.ext (one_smul G b.val)
  mul_smul g h b := Subtype.ext (mul_smul g h b.val)

variable [TopologicalSpace X] [ContinuousConstSMul G X]

instance configurationSpaceContinuousConstSMul :
    ContinuousConstSMul G (ConfigurationSpace m X) where
  continuous_const_smul g :=
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

omit [ContinuousConstSMul G X] in
theorem isCompact_configurationSpace_lift
    {F : Set (Fin m → X)} (hF : IsCompact F) (hFc : F ⊆ configuration m X) :
    IsCompact ((Subtype.val : ConfigurationSpace m X → (Fin m → X)) ⁻¹' F) := by
  rw [IsEmbedding.subtypeVal.isCompact_iff]
  have heq : Subtype.val ''
      ((Subtype.val : ConfigurationSpace m X → (Fin m → X)) ⁻¹' F) = F := by
    ext b
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hb
      exact ⟨⟨b, hFc hb⟩, hb, rfl⟩
  rwa [heq]

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem invariant_configurationSpace_lift
    {F : Set (Fin m → X)} (hF : invariant G F) :
    invariant G ((Subtype.val : ConfigurationSpace m X → (Fin m → X)) ⁻¹' F) := by
  intro g b hb
  exact hF g hb

end VeechDichotomy
