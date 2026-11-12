module

public import VeechDichotomy.HyperbolicDirichletCorners
public import VeechDichotomy.HyperbolicRegularCenters

/-! Fixed points of genuinely nontrivial discrete SL2 actions are finite
on compact sets. Proper discontinuity leaves finitely many possible
labels fixing a point in the compact set; actual fixed-point uniqueness
leaves finitely many points. Together with the actual independent-normal
corners this gives compact finiteness of the full vertex-candidate set,
including elliptic side points and excluding the trivially acting kernel. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicEllipticLocalFiniteness

open LinearGroup HyperbolicDirichletRegions HyperbolicDirichletCorners HyperbolicRegularCenters Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def ellipticPoints (Γ : Subgroup SL2) : Set ℍ :=
  {z | ∃ γ : Γ, (¬ ∀ w : ℍ, γ • w = w) ∧ γ • z = z}

theorem finite_inter_compact (Γ : Subgroup SL2) [DiscreteTopology Γ] {K : Set ℍ} (hK : IsCompact K) :
    (ellipticPoints Γ ∩ K).Finite := by
  let S : Set Γ := {γ | (((γ • ·) '' K) ∩ K).Nonempty ∧ ¬ ∀ w : ℍ, γ • w = w}
  have hS : S.Finite := (ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hK).subset (fun _ hg => hg.1)
  let : Finite S := hS.to_subtype
  have hf : (⋃ γ : S, {z : ℍ | γ.val • z = z}).Finite :=
    Set.finite_iUnion (fun γ => (fixedSet_subsingleton γ.val.val γ.property.2).finite)
  apply hf.subset
  rintro z ⟨⟨γ, hnontrivial, hfix⟩, hzK⟩
  have hγ : γ ∈ S := ⟨⟨z, ⟨z, hzK, hfix⟩, hzK⟩, hnontrivial⟩
  exact mem_iUnion.mpr ⟨⟨γ, hγ⟩, hfix⟩

def vertexCandidates (Γ : Subgroup SL2) (p : ℍ) : Set ℍ :=
  corners Γ p ∪ (region Γ p ∩ ellipticPoints Γ)

theorem vertexCandidates_finite_inter_compact (Γ : Subgroup SL2) [DiscreteTopology Γ]
    (p : ℍ) {K : Set ℍ} (hK : IsCompact K) : (vertexCandidates Γ p ∩ K).Finite := by
  apply ((HyperbolicDirichletCorners.finite_inter_compact Γ p hK).union
    (finite_inter_compact Γ hK)).subset
  rintro z ⟨hz, hzK⟩
  rcases hz with hcorner | helliptic
  · exact Or.inl ⟨hcorner, hzK⟩
  · exact Or.inr ⟨helliptic.2, hzK⟩

end VeechDichotomy.HyperbolicEllipticLocalFiniteness
