module

public import VeechDichotomy.DirichletCompactTruncations

/-! An actual closed subset of an actual Dirichlet region is compact
if its actual Klein closure avoids every actual ideal endpoint. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletClosedSubsetCompactness

open LinearGroup Set HyperbolicDirichletRegions HyperbolicKleinMap DirichletKleinClosure
open DirichletIdealRadialPoints
open scoped UpperHalfPlane

theorem compact_of_ideal_avoiding (Γ : Subgroup SL2) (p : ℍ) (S : Set ℍ) (hS : IsClosed S)
    (hSD : S ⊆ region Γ p) (havoid : ∀ u ∈ idealBoundary Γ p, u ∉ closure (point '' S)) : IsCompact S := by
  have hsub : closure (point '' S) ⊆ closedRegion Γ p := closure_mono (image_mono hSD)
  have hc : IsCompact (closure (point '' S)) :=
    (isCompact_closedRegion Γ p).of_isClosed_subset isClosed_closure hsub
  have hpre : point ⁻¹' closure (point '' S) = S := by
    rw [← DirichletCompactTruncations.point_isEmbedding.closure_eq_preimage_closure_image, hS.closure_eq]
  have heq : closure (point '' S) = point '' S := by
    apply Subset.antisymm
    · intro u hu
      rcases mem_or_ideal Γ p (hsub hu) with ⟨z, _, rfl⟩ | hi
      · refine ⟨z, ?_, rfl⟩
        exact hpre ▸ hu
      · exact False.elim (havoid u hi hu)
    · exact subset_closure
  apply DirichletCompactTruncations.point_isEmbedding.isCompact_iff.mpr
  rwa [← heq]

end VeechDichotomy.DirichletClosedSubsetCompactness
