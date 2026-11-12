module

public import VeechDichotomy.IdealEndpointHeightNormalization
public import VeechDichotomy.NativeIdealInfinityParabolic

/-! Every actual ideal endpoint of an actual regular-center native
lattice Dirichlet region has an actual nontrivial parabolic in the
group, given as an explicit conjugate of a nonzero upper unipotent. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeIdealEndpointParabolic

open LinearGroup HyperbolicRegularCenters DirichletIdealRadialPoints
open NativeLatticeConjugation IdealEndpointHeightNormalization
open scoped UpperHalfPlane

theorem exists_parabolic (Γ : Subgroup SL2) (hΓ : NativeVeech.IsLattice Γ) (p : ℍ) (hp : RegularCenter Γ p)
    {u : ℂ} (hu : u ∈ idealBoundary Γ p) :
    ∃ (B : SL2) (s : ℝ), SL2BottomRowEndpoints.endpoint B = u ∧ s ≠ 0 ∧
      B⁻¹ * IdealInfinityStabilizers.upper s * B ∈ Γ := by
  obtain ⟨B, he⟩ := exists_normalizer u hu.2
  have hI := ideal_conjugate Γ p B (by simpa only [he] using hu)
  obtain ⟨s, hs, hmem⟩ := NativeIdealInfinityParabolic.exists_nonzero_upper (conjugate Γ B)
    (isLattice_conjugate Γ hΓ B) (B • p) (regular_conjugate Γ p hp B) hI
  exact ⟨B, s, he, hs, hmem⟩

end VeechDichotomy.NativeIdealEndpointParabolic
