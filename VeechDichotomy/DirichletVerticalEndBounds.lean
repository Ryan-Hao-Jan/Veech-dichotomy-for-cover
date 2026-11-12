module

public import VeechDichotomy.DirichletFiniteClosurePresentation
public import VeechDichotomy.IdealInfinityBoundaryArcs

/-! At an actual isolated ideal endpoint at infinity, every genuine
finite presentation has actual vertical constraints in both directions.
Otherwise actual unit-circle arcs on one side would supply additional
ideal points arbitrarily close to the endpoint, contradicting finiteness. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DirichletVerticalEndBounds

open LinearGroup NativeVeech Set Filter Topology HyperbolicDirichletRegions HyperbolicRegularCenters
open HyperbolicKleinHalfPlanes HyperbolicBisectorNull DirichletIdealRadialPoints DirichletIdealInfinity
open IdealInfinityBoundaryArcs
open scoped UpperHalfPlane

theorem exists_signed_vertical (Γ : Subgroup SL2) (p : ℍ) (S : Finset Γ)
    (hS : region Γ p = {z : ℍ | ∀ γ ∈ S, dist z p ≤ dist z (γ • p)})
    (hf : (idealBoundary Γ p).Finite) (hI : Complex.I ∈ idealBoundary Γ p) (σ : ℝ) (hσ : σ ≠ 0) :
    ∃ γ ∈ S, leading p (γ • p) = 0 ∧ 0 < σ * linear p (γ • p) := by
  classical
  by_contra hnone
  push Not at hnone
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ γ ∈ S, 0 < t → affineForm p (γ • p) (arc (σ * t)) ≤ 0 := by
    apply S.finite_toSet.eventually_all.mpr
    intro γ hγ
    by_cases hfix : γ • p = p
    · exact Eventually.of_forall (fun t _ => by rw [hfix]; simp [affineForm, leading, HyperbolicBisectorNull.linear, constant])
    · apply eventually_halfPlane p (γ • p) σ (sub_nonpos.mpr (orbit_height_le Γ p hI γ))
      intro ha
      have hb : linear p (γ • p) ≠ 0 :=
        (coefficient_nontrivial (fun he => hfix he.symm)).resolve_left (not_ne_iff.mpr ha)
      exact lt_of_le_of_ne (hnone γ hγ ha) (mul_ne_zero hσ hb)
  have hnot : Complex.I ∉ idealBoundary Γ p \ {Complex.I} := fun h => h.2 (mem_singleton _)
  have hnhds : (idealBoundary Γ p \ {Complex.I})ᶜ ∈ 𝓝 Complex.I :=
    hf.sdiff.isClosed.isOpen_compl.mem_nhds hnot
  have havoid := (arc_tendsto σ).eventually hnhds
  obtain ⟨t, ht, hconstraints, hout⟩ := (hev.and havoid).exists_gt
  have hideal := DirichletFiniteClosurePresentation.ideal_mem_of_constraints Γ p S hS
    (arc (σ * t)) (norm_arc _) (fun γ hγ => hconstraints γ hγ ht)
  exact hout ⟨hideal, by simpa only [mem_singleton_iff] using arc_ne_I (mul_ne_zero hσ ht.ne')⟩

theorem exists_vertical_pair (Γ : Subgroup SL2) (hΓ : IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (hI : Complex.I ∈ idealBoundary Γ p) :
    ∃ γ δ : Γ, leading p (γ • p) = 0 ∧ linear p (γ • p) < 0 ∧
      leading p (δ • p) = 0 ∧ 0 < linear p (δ • p) := by
  obtain ⟨S, hS⟩ := NativeDirichletFinitePresentation.exists_finite_constraints Γ hΓ p hp
  have hf := NativeDirichletFiniteIdealBoundary.idealBoundary_finite Γ hΓ p
  obtain ⟨γ, _, hγa, hγb⟩ := exists_signed_vertical Γ p S hS hf hI (-1) (by norm_num)
  obtain ⟨δ, _, hδa, hδb⟩ := exists_signed_vertical Γ p S hS hf hI 1 one_ne_zero
  exact ⟨γ, δ, hγa, by simpa only [neg_one_mul, neg_pos] using hγb, hδa, by simpa only [one_mul] using hδb⟩

end VeechDichotomy.DirichletVerticalEndBounds
