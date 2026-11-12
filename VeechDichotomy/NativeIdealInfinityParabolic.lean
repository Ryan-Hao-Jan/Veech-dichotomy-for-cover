module

public import VeechDichotomy.MaximalHeightCenters
public import VeechDichotomy.IdealInfinityRelativeMatrices
public import Mathlib.Data.Fintype.Pigeonhole

/-! Every actual ideal endpoint at physical infinity of an actual
regular-center native lattice Dirichlet region has an actual nonzero
upper unipotent in the group. Infinitely many maximal-height centers
and finitely many actual ideal endpoints supply the genuine matrices. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeIdealInfinityParabolic

open LinearGroup Set HyperbolicRegularCenters DirichletIdealRadialPoints MaximalHeightCenters
open scoped UpperHalfPlane

def representative (Γ : Subgroup SL2) (p : ℍ) (q : centers Γ p) : Γ := Classical.choose q.property.1

theorem representative_spec (Γ : Subgroup SL2) (p : ℍ) (q : centers Γ p) :
    representative Γ p q • p = q.val := Classical.choose_spec q.property.1

theorem representative_height (Γ : Subgroup SL2) (p : ℍ) (q : centers Γ p) :
    (representative Γ p q • p).im = p.im := by rw [representative_spec]; exact q.property.2

def idealMap (Γ : Subgroup SL2) (p : ℍ) (hI : Complex.I ∈ idealBoundary Γ p)
    (q : centers Γ p) : idealBoundary Γ p :=
  ⟨SL2BottomRowEndpoints.endpoint (representative Γ p q),
    SL2BottomRowEndpoints.endpoint_mem_ideal Γ p hI _ (representative_height Γ p q)⟩

theorem exists_nonzero_upper (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    (hI : Complex.I ∈ idealBoundary Γ p) :
    ∃ s : ℝ, s ≠ 0 ∧ IdealInfinityStabilizers.upper s ∈ Γ := by
  let : Infinite (centers Γ p) := Set.infinite_coe_iff.mpr (centers_infinite Γ hΓ p hp hI)
  let : Finite (idealBoundary Γ p) := (NativeDirichletFiniteIdealBoundary.idealBoundary_finite Γ hΓ p).to_subtype
  obtain ⟨q, r, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite (idealMap Γ p hI)
  have hep : SL2BottomRowEndpoints.endpoint (representative Γ p q) =
      SL2BottomRowEndpoints.endpoint (representative Γ p r) := congrArg Subtype.val he
  apply IdealInfinityRelativeMatrices.exists_upper_of_equal_endpoints Γ p hI _ _ hep
  intro hcenters
  rw [representative_spec, representative_spec] at hcenters
  exact hne (Subtype.ext hcenters)

end VeechDichotomy.NativeIdealInfinityParabolic
