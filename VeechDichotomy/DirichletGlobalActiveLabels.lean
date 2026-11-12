module

public import VeechDichotomy.DirichletFiniteFaces

/-! Only finitely many actual group labels have a bisector touching
the actual Dirichlet region. The actual clipped bisectors form a finite
family; a point chosen on each realized face puts every label of that
face in one of the already proved finite point-incidence sets. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletGlobalActiveLabels

open LinearGroup NativeVeech Set HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicDirichletIncidence HyperbolicKleinMap DirichletFiniteFaces DirichletKleinClosure
open scoped UpperHalfPlane

def realizedFaces (Γ : Subgroup SL2) (p : ℍ) : Set (Set ℂ) :=
  {F | F ∈ range (face Γ p) ∧ ∃ z ∈ region Γ p, point z ∈ F}

theorem realizedFaces_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    (realizedFaces Γ p).Finite := (faces_finite Γ hΓ p hp).subset (fun _ h => h.1)

def pointOnFace (Γ : Subgroup SL2) (p : ℍ) (F : realizedFaces Γ p) : ℍ :=
  Classical.choose F.property.2

theorem pointOnFace_mem (Γ : Subgroup SL2) (p : ℍ) (F : realizedFaces Γ p) :
    pointOnFace Γ p F ∈ region Γ p ∧ point (pointOnFace Γ p F) ∈ F.val :=
  Classical.choose_spec F.property.2

theorem activeLabels_region_finite (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p) :
    (activeLabels Γ p (region Γ p)).Finite := by
  let : DiscreteTopology Γ := hΓ.1
  let : Finite (realizedFaces Γ p) := (realizedFaces_finite Γ hΓ p hp).to_subtype
  have hf : (⋃ F : realizedFaces Γ p, activeLabels Γ p {pointOnFace Γ p F}).Finite :=
    finite_iUnion (fun _ => activeLabels_finite Γ p isCompact_singleton)
  apply hf.subset
  rintro γ ⟨z, hz, _, hd⟩
  have hpoint : point z ∈ face Γ p γ :=
    ⟨subset_closure ⟨z, hz, rfl⟩, (HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) z).mp hd⟩
  let F : realizedFaces Γ p := ⟨face Γ p γ, ⟨mem_range_self γ, z, hz, hpoint⟩⟩
  have hF := pointOnFace_mem Γ p F
  have heq : dist (pointOnFace Γ p F) p = dist (pointOnFace Γ p F) (γ • p) :=
    (HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) _).mpr hF.2.2
  exact mem_iUnion.mpr ⟨F, pointOnFace Γ p F, mem_singleton _, hF.1, heq⟩

end VeechDichotomy.DirichletGlobalActiveLabels
