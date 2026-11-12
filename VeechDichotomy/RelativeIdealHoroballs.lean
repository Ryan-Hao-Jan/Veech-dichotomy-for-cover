module

public import VeechDichotomy.NativeIdealCuspCoordinates
public import VeechDichotomy.TriangularHeightComparison
public import VeechDichotomy.RelativeHoroballSeparation

/-! Horoballs normalized by the actual reference center height are
compatible across actual ideal endpoints. At sufficient normalized
depth, two translates that overlap are exactly the same horoball. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.RelativeIdealHoroballs

open LinearGroup Set HyperbolicDirichletRegions DirichletIdealRadialPoints
open NativeLatticeConjugation IdealEndpointHeightNormalization IdealInfinityStabilizers
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def relative (B C γ : SL2) : SL2 := B * γ * C⁻¹
def horoball (p : ℍ) (B : SL2) (R : ℝ) : Set ℍ := {z | R * (B • p).im < (B • z).im}

theorem isOpen_horoball (p : ℍ) (B : SL2) (R : ℝ) : IsOpen (horoball p B R) :=
  NativeIdealCuspCoordinates.isOpen_horoball B _

theorem relative_smul (B C γ : SL2) (z : ℍ) : relative B C γ • (C • z) = B • (γ • z) := by
  unfold relative
  rw [mul_smul, inv_smul_smul, mul_smul]

theorem relative_inv_smul (B C γ : SL2) (z : ℍ) : (relative B C γ)⁻¹ • (B • z) = C • (γ⁻¹ • z) := by
  have he : (relative B C γ)⁻¹ * B = C * γ⁻¹ := by unfold relative; group
  rw [← mul_smul, he, mul_smul]

theorem compatible (Γ : Subgroup SL2) (p : ℍ) (B C : SL2)
    (hB : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p)
    (hC : SL2BottomRowEndpoints.endpoint C ∈ idealBoundary Γ p) (γ : Γ)
    (hc : (relative B C γ) 1 0 = 0) (R : ℝ) (z : ℍ) :
    γ • z ∈ horoball p B R ↔ z ∈ horoball p C R := by
  have hforward : (relative B C γ • (C • p)).im ≤ (B • p).im := by
    rw [relative_smul]
    exact (ideal_iff_maximal_height Γ p B).mp hB γ
  have hbackward : ((relative B C γ)⁻¹ • (B • p)).im ≤ (C • p).im := by
    rw [relative_inv_smul]
    exact (ideal_iff_maximal_height Γ p C).mp hC γ⁻¹
  have he := TriangularHeightComparison.normalized_horoball_iff (relative B C γ) (C • p) (B • p)
    (C • z) R hc hforward hbackward
  rw [relative_smul] at he
  exact he

theorem image_eq_of_relative_zero (Γ : Subgroup SL2) (p : ℍ) (B C : SL2)
    (hB : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p)
    (hC : SL2BottomRowEndpoints.endpoint C ∈ idealBoundary Γ p) (γ : Γ)
    (hc : (relative B C γ) 1 0 = 0) (R : ℝ) :
    (fun z : ℍ => γ • z) '' horoball p C R = horoball p B R := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (compatible Γ p B C hB hC γ hc R z).mpr hz
  · intro w hw
    refine ⟨γ⁻¹ • w, ?_, smul_inv_smul γ w⟩
    apply (compatible Γ p B C hB hC γ hc R (γ⁻¹ • w)).mp
    simpa only [smul_inv_smul] using hw

theorem overlap_relative_zero (Γ : Subgroup SL2) (p : ℍ) (B C : SL2)
    (hB : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p)
    (τ : ℝ) (hτ : 0 < τ) (hmem : upper τ ∈ conjugate Γ C)
    (R : ℝ) (hR : 0 < R) (hdepth : τ ^ 2 + (C • p).im ^ 2 ≤ R ^ 2 * (C • p).im ^ 2)
    (γ : Γ) (z : ℍ) (hz : z ∈ horoball p C R) (hg : γ • z ∈ horoball p B R) :
    (relative B C γ) 1 0 = 0 := by
  have hheight (n : ℤ) : ((relative B C γ * upper ((n : ℝ) * τ)) • (C • p)).im ≤ (B • p).im := by
    let δ : Γ := toOriginal Γ C
      ⟨upper ((n : ℝ) * τ), UpperUnipotentPowers.integer_multiple_mem (conjugate Γ C) τ hmem n⟩
    have he : (relative B C γ * upper ((n : ℝ) * τ)) * C = B * (γ : SL2) * (δ : SL2) := by
      dsimp only [relative, δ, toOriginal]
      group
    rw [← mul_smul, he, mul_smul, mul_smul]
    have hh := (ideal_iff_maximal_height Γ p B).mp hB (γ * δ)
    simpa only [mul_smul] using! hh
  have he := RelativeHoroballSeparation.overlap_lower_left_zero (relative B C γ) (C • p)
    τ (B • p).im R hτ (B • p).im_pos hR hheight hdepth (C • z) hz
  apply he
  rw [relative_smul]
  exact hg

theorem image_eq_or_disjoint (Γ : Subgroup SL2) (p : ℍ) (B C : SL2)
    (hB : SL2BottomRowEndpoints.endpoint B ∈ idealBoundary Γ p)
    (hC : SL2BottomRowEndpoints.endpoint C ∈ idealBoundary Γ p)
    (τ : ℝ) (hτ : 0 < τ) (hmem : upper τ ∈ conjugate Γ C)
    (R : ℝ) (hR : 0 < R) (hdepth : τ ^ 2 + (C • p).im ^ 2 ≤ R ^ 2 * (C • p).im ^ 2) (γ : Γ) :
    (fun z : ℍ => γ • z) '' horoball p C R = horoball p B R ∨
      Disjoint ((fun z : ℍ => γ • z) '' horoball p C R) (horoball p B R) := by
  by_cases hc : (relative B C γ) 1 0 = 0
  · exact Or.inl (image_eq_of_relative_zero Γ p B C hB hC γ hc R)
  · apply Or.inr
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ hg
    exact hc (overlap_relative_zero Γ p B C hB τ hτ hmem R hR hdepth γ z hz hg)

end VeechDichotomy.RelativeIdealHoroballs
