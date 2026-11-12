module

public import VeechDichotomy.HyperbolicDirichletIncidence
public import VeechDichotomy.HyperbolicKleinHalfPlanes
public import Mathlib.Tactic.LinearCombination

/-! Actual corners defined by two independent active Dirichlet normals
are finite on every compact subset of the genuine hyperbolic plane.
An explicit two-by-two determinant gives uniqueness of each intersection;
the actual finite active-label set leaves finitely many possible pairs.
No polygon finiteness or vertex-local-finiteness oracle is assumed. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicDirichletCorners

open LinearGroup HyperbolicDirichletRegions HyperbolicDirichletIncidence
open HyperbolicKleinMap HyperbolicKleinHomeomorph HyperbolicKleinHalfPlanes
open HyperbolicBisectorNull Set
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

theorem affine_intersection_subsingleton (c₀ a₀ b₀ c₁ a₁ b₁ : ℝ)
    (hd : a₀ * b₁ - a₁ * b₀ ≠ 0) :
    {u : ℂ | c₀ + a₀ * u.re + b₀ * u.im = 0 ∧ c₁ + a₁ * u.re + b₁ * u.im = 0}.Subsingleton := by
  intro u hu v hv
  have h₀ : a₀ * (u.re - v.re) + b₀ * (u.im - v.im) = 0 := by nlinarith only [hu.1, hv.1]
  have h₁ : a₁ * (u.re - v.re) + b₁ * (u.im - v.im) = 0 := by nlinarith only [hu.2, hv.2]
  have hre : (a₀ * b₁ - a₁ * b₀) * (u.re - v.re) = 0 := by linear_combination b₁ * h₀ - b₀ * h₁
  have him : (a₀ * b₁ - a₁ * b₀) * (u.im - v.im) = 0 := by linear_combination a₀ * h₁ - a₁ * h₀
  apply Complex.ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hre).resolve_left hd)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp him).resolve_left hd)

def normalRe (p q : ℍ) : ℝ := linear p q / 2
def normalIm (p q : ℍ) : ℝ := (leading p q - constant p q) / 2
def normalDet (p q r : ℍ) : ℝ := normalRe p q * normalIm p r - normalRe p r * normalIm p q

def intersection (p q r : ℍ) : Set ℍ :=
  {z | affineForm p q (point z) = 0 ∧ affineForm p r (point z) = 0}

theorem intersection_subsingleton {p q r : ℍ} (hd : normalDet p q r ≠ 0) :
    (intersection p q r).Subsingleton := by
  have hs : {u : ℂ | affineForm p q u = 0 ∧ affineForm p r u = 0}.Subsingleton :=
    affine_intersection_subsingleton ((leading p q + constant p q) / 2) (normalRe p q) (normalIm p q)
      ((leading p r + constant p r) / 2) (normalRe p r) (normalIm p r) hd
  intro z hz w hw
  apply homeomorph.injective
  apply Subtype.ext
  exact hs hz hw

def corners (Γ : Subgroup SL2) (p : ℍ) : Set ℍ :=
  {z | z ∈ region Γ p ∧ ∃ γ δ : Γ, normalDet p (γ • p) (δ • p) ≠ 0 ∧ z ∈ intersection p (γ • p) (δ • p)}

theorem finite_inter_compact (Γ : Subgroup SL2) [DiscreteTopology Γ] (p : ℍ)
    {K : Set ℍ} (hK : IsCompact K) : (corners Γ p ∩ K).Finite := by
  let S := activeLabels Γ p K
  have hS : S.Finite := activeLabels_finite Γ p hK
  let J : Set (Γ × Γ) := {g | g.1 ∈ S ∧ g.2 ∈ S ∧ normalDet p (g.1 • p) (g.2 • p) ≠ 0}
  have hJ : J.Finite := (hS.prod hS).subset (fun _ hg => ⟨hg.1, hg.2.1⟩)
  let : Finite J := hJ.to_subtype
  have hf : (⋃ g : J, intersection p (g.val.1 • p) (g.val.2 • p)).Finite :=
    Set.finite_iUnion (fun g => (intersection_subsingleton g.property.2.2).finite)
  apply hf.subset
  intro z hz
  obtain ⟨hzD, γ, δ, hd, hactive⟩ := hz.1
  have hγ : γ ∈ S := ⟨z, hz.2, hzD, (HyperbolicKleinHalfPlanes.dist_eq_iff p (γ • p) z).mpr hactive.1⟩
  have hδ : δ ∈ S := ⟨z, hz.2, hzD, (HyperbolicKleinHalfPlanes.dist_eq_iff p (δ • p) z).mpr hactive.2⟩
  exact mem_iUnion.mpr ⟨⟨(γ, δ), ⟨hγ, hδ, hd⟩⟩, hactive⟩

end VeechDichotomy.HyperbolicDirichletCorners
